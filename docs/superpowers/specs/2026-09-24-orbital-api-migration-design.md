# Design: Migrate TLE source from D1 to Orbital Data API

**Date:** 2026-09-24
**Status:** Approved design, pending implementation
**Scope:** Cloudflare Worker (`cf/`) only. Legacy Python stack untouched.

## Problem

The Cloudflare Worker's remote D1 database is exceeding Cloudflare's free-tier
**write** limits. The cause is the daily ingestion cron (`scheduled()` →
`refresh()`), which bulk-upserts every satellite it can find:

- 7 CelesTrak TLE groups (`weather, noaa, resource, stations, active, visual,
  science`) via `INSERT OR REPLACE` into `tle_latest`, **plus**
- the full CelesTrak SATCAT (~60k rows) into `satellites`,

every day. That is tens of thousands of writes/day against a 100k/day free cap,
and it grows with the catalog.

## Decision

Replace the "bulk-seed CelesTrak into D1, refresh daily" subsystem with an
**on-demand, stateless proxy** over the project owner's own API,
`https://orbital-data-api.davidhsu.cc` (base `…/api/v1`). **D1 is removed
entirely.** Request de-duplication uses the **Cloudflare Cache API**
(`caches.default`), which is free and incurs no D1 I/O.

Two alternatives were considered and rejected:

- **D1 as a lazy read-through cache** — reduces upstream calls but reintroduces
  writes (the exact failure mode we are escaping) and adds schema/TTL
  complexity. Rejected after discussion.
- **D1 only for catalog search** — the SATCAT catalog table is the *largest*
  write source, so caching it in D1 is backwards.

Net effect: D1 writes drop to **zero**, ~350 lines of ingestion code are
deleted, and predictions become *more* accurate (see `nearest` below).

## The Orbital Data API

- **Base:** `https://orbital-data-api.davidhsu.cc/api/v1`
- **Auth:** `X-Api-Key: <key>` header. Required for `/gp/*` and `/catalog/*`;
  not required for `/explore/*` and `/status`.
- **Output formats:** `?format=tle|2le|json|xml|kvn|csv`. We request **`format=json`
  (OMM)** as the single source for propagation — see OMM Support below. This also
  removes the NORAD > 99,999 limitation entirely (no 5-char TLE field involved).

Endpoints used:

| Purpose | Endpoint |
|---|---|
| Latest element set | `GET /gp/{norad}?format=json` |
| Element set nearest a date | `GET /gp/{norad}/nearest?epoch=<ISO date>&format=json` |
| Catalog search | `GET /catalog?search=<q>` (JSON) |

## Architecture

The Worker becomes a thin, cached proxy plus the existing `satellite.js`
prediction engine. No persistent storage.

```
client → Worker route → api-client (Cache API check)
                          ├─ cache hit  → return cached upstream response
                          └─ cache miss → fetch Orbital Data API (X-Api-Key)
                                          → store in Cache API
                                          → return
       → predict.ts (unchanged) for /api/predict/overpass
```

### Route mapping (`cf/src/index.ts`)

| Worker route | Upstream call | Cache TTL |
|---|---|---|
| `GET /api/satellites?q=` | `GET /catalog?search=<q>` | ~1 h |
| `GET /api/tles/latest/:norad_id` | `GET /gp/{norad}?format=json` | ~6 h |
| `GET /api/predict/overpass` | `GET /gp/{norad}/nearest?epoch=<start_date>&format=json` | historical: ~immutable; current: ~6 h |

The `/api/tles/latest` route still returns TLE lines in its JSON response for
backward compat with the frontend; those lines are produced from the OMM via the
existing `ommToTleLines` helper (NORAD ≤ 99,999) or omitted for higher IDs.
Propagation itself never uses them — it uses `omm2satrec` (see OMM Support).

- `/api/predict/overpass` fetches the element set **nearest the requested
  start date** rather than the latest. This lets us **delete the 7-day
  staleness clamp** currently at `index.ts:69-78` — accuracy is now handled by
  the data layer.
- `POST /api/refresh` and the `scheduled()` cron handler are **removed**.

### OMM Support — native OMM → satrec (no TLE text round-trip)

The Worker builds the SGP4 propagator (`satrec`) **directly from OMM elements**,
rather than synthesizing fixed-width TLE text and re-parsing it. This is cleaner
(no lossy truncation, no checksum/exponent formatting, no Alpha-5 encoding) and
removes the NORAD > 99,999 limitation outright — `satnum` is an opaque string in
SGP4 and is never used in the orbital math.

satellite.js 5.0.0 exports only `twoline2satrec` and `sgp4`, but `sgp4init`
(and `jday`) are reachable via deep CJS import:

```ts
import sgp4init from "satellite.js/lib/propagation/sgp4init";
// jday likewise from satellite.js internals, pinned to the installed version
```

New function `omm2satrec(omm)` mirrors exactly what `twoline2satrec` does before
its `sgp4init` call, reading numeric fields straight from OMM:

| satrec field | OMM source | conversion |
|---|---|---|
| `satnum` | `NORAD_CAT_ID` | string, no length limit |
| `no` | `MEAN_MOTION` | `÷ (1440 / 2π)` → rad/min |
| `ecco` | `ECCENTRICITY` | as-is |
| `inclo` | `INCLINATION` | `× deg2rad` |
| `nodeo` | `RA_OF_ASC_NODE` | `× deg2rad` |
| `argpo` | `ARG_OF_PERICENTER` | `× deg2rad` |
| `mo` | `MEAN_ANOMALY` | `× deg2rad` |
| `bstar` | `BSTAR` | as-is |
| `jdsatepoch` | `EPOCH` (ISO) | via satellite.js `jday`; `epoch = jdsatepoch − 2433281.5` |

**Isolation requirement:** the deep import and `sgp4init` call live solely inside
`omm2satrec`. If the pinned internal path ever breaks, only this one function
changes (swap to a vendored `sgp4init` port — option C — without touching
callers). The satellite.js version is pinned in `package.json`.

**Parity:** `omm2satrec` output must produce the same `sgp4` positions as the
pre-migration `twoline2satrec` path for a known satellite/epoch (see Testing).

### New module: `cf/src/api-client.ts`

A small typed client. One responsibility: talk to the Orbital Data API and
cache responses. Interface:

```ts
getLatestOmm(env, noradId): Promise<OmmRecord | null>
getNearestOmm(env, noradId, epochDate): Promise<OmmRecord | null>
searchCatalog(env, query, limit): Promise<SatelliteSearchResult[]>
```

The GP functions return the raw `OmmRecord`; callers pass it to `omm2satrec` for
propagation (and, for `/api/tles/latest`, to `ommToTleLines` for display).

Each function:
1. Builds the upstream URL (`format=json`).
2. Checks `caches.default` keyed by that URL.
3. On miss, `fetch`es with header `X-Api-Key: env.ORBITAL_API_KEY`.
4. Stores the response in the cache with a `Cache-Control: max-age=<ttl>`
   derived from a single **freshness-policy function** (see below).
5. Parses the JSON body and returns typed data.

### Freshness policy (owner-authored)

TTL selection is isolated in one small function so the freshness-vs-load
trade-off is explicit and easy to change:

```ts
// Returns cache max-age in seconds for a given query.
function cacheTtlSeconds(kind: "latest" | "search" | "historical",
                         epochDate?: string): number
```

Default intent: `search` ~3600, `latest` ~21600 (6 h), `historical`
(epoch clearly in the past) very long / effectively immutable. Exact values —
and whether they vary by orbit regime — are the owner's call and will be filled
in during implementation.

### Config / secrets

- `cf/wrangler.toml`: remove `[[d1_databases]]` and `[triggers]`. Keep
  `[assets]`. Document (comment only) that `ORBITAL_API_KEY` is a secret.
- Secret set via `wrangler secret put ORBITAL_API_KEY` (local dev via
  `.dev.vars`, git-ignored).
- `Env` interface (`types.ts`) changes: drop `DB: D1Database`, add
  `ORBITAL_API_KEY: string`.

## Files touched

**Deleted:** `cf/src/seed.ts`, `cf/src/db.ts`, `cf/migrations/`.

**Added:** `cf/src/api-client.ts`.

**Changed:**
- `cf/src/index.ts` — rewrite the 3 data routes to use `api-client`; remove
  `/api/refresh`, `scheduled()`, and the staleness clamp. Build the propagator
  via `omm2satrec` for both the latest and nearest paths.
- `cf/src/types.ts` — update `Env` (drop `DB`, add `ORBITAL_API_KEY`); trim D1
  row types; keep `OmmRecord`, `PredictionConfig`, `PassResult`,
  `PredictionResult`, `DEFAULT_CONFIG`.
- `cf/src/tle-parse.ts` — add `omm2satrec(omm)` (deep-imports `sgp4init`/`jday`);
  keep `parseOmmRecord`, `epochFromOmm`, and `ommToTleLines` (now only for the
  backward-compat TLE lines in the `/api/tles/latest` response, NORAD ≤ 99,999).
- `cf/wrangler.toml` — remove D1 + cron.
- `cf/package.json` — remove `db:migrate*` and `seed` scripts; pin `satellite.js`
  to the installed version (deep import relies on its internal layout).

**Unchanged:** `cf/src/predict.ts`, `cf/src/solar.ts`, `cf/public/index.html`.

## Error handling

- Upstream non-200 → map to Worker HTTP status: 404 from API → `404 NORAD not
  found`; 401/403 → `502` with a "data source auth failed" message (do not leak
  the key); other 5xx/network → `502 upstream unavailable`.
- Malformed/incomplete OMM (missing a required element field) → `502 bad upstream
  data`.
- `norad_id` missing/invalid → `400` (unchanged).

Note: NORAD > 99,999 is now fully supported for prediction via `omm2satrec`; the
only degradation for those IDs is the omitted TLE line strings in the
`/api/tles/latest` response (display-only).

## Testing

- **Unit:** `api-client` with a mocked `fetch` — URL construction (incl.
  `epoch` param and `X-Api-Key` header), cache hit vs. miss, TLE/JSON parsing,
  and error-status mapping. `cacheTtlSeconds` returns expected buckets.
- **Prediction parity (guard):** for a known satellite (e.g. ISS 25544), the
  satrec produced by `omm2satrec(omm)` yields the same `sgp4` position/velocity
  (within float tolerance) as `twoline2satrec(line1, line2)` for the equivalent
  TLE — confirms the OMM-native path matches the text path, and that
  `runPrediction` output is unchanged.
- **High-NORAD:** `omm2satrec` succeeds and propagates for a NORAD > 99,999
  object (the case that previously returned 501).
- **Manual/E2E:** `wrangler dev` with `.dev.vars` key set; exercise all three
  routes and confirm Cache API hits on repeat (via `cf-cache-status` or logs).

## Out of scope

- Any change to the legacy Python stack or `cf/public/index.html`.
- Migrating off the deep `sgp4init`/`jday` import to a vendored port (option C) —
  deferred; the design isolates `omm2satrec` so this is a later localized swap.
