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
- **Output formats:** `?format=tle|2le|json|xml|kvn|csv`. `format=tle` returns a
  3-line TLE (name + line1 + line2) — feeds directly into
  `satellite.js.twoline2satrec`, no OMM→TLE conversion needed.
- **Caveat:** NORAD IDs > 99,999 cannot use `format=tle` (5-char field). Those
  fall back to JSON/OMM — the same OMM-only limitation the Worker already has;
  not a regression.

Endpoints used:

| Purpose | Endpoint |
|---|---|
| Latest element set | `GET /gp/{norad}?format=tle` |
| Element set nearest a date | `GET /gp/{norad}/nearest?epoch=<ISO date>&format=tle` |
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
| `GET /api/tles/latest/:norad_id` | `GET /gp/{norad}?format=tle` | ~6 h |
| `GET /api/predict/overpass` | `GET /gp/{norad}/nearest?epoch=<start_date>&format=tle` | historical: ~immutable; current: ~6 h |

- `/api/predict/overpass` fetches the element set **nearest the requested
  start date** rather than the latest. This lets us **delete the 7-day
  staleness clamp** currently at `index.ts:69-78` — accuracy is now handled by
  the data layer.
- `POST /api/refresh` and the `scheduled()` cron handler are **removed**.

### New module: `cf/src/api-client.ts`

A small typed client. One responsibility: talk to the Orbital Data API and
cache responses. Interface:

```ts
getTle(env, noradId): Promise<TleLines | null>
getNearestTle(env, noradId, epochDate): Promise<TleLines | null>
searchCatalog(env, query, limit): Promise<SatelliteSearchResult[]>
```

where `TleLines = { name: string; line1: string; line2: string; epoch_utc: string }`.

Each function:
1. Builds the upstream URL.
2. Checks `caches.default` keyed by that URL.
3. On miss, `fetch`es with header `X-Api-Key: env.ORBITAL_API_KEY`.
4. Stores the response in the cache with a `Cache-Control: max-age=<ttl>`
   derived from a single **freshness-policy function** (see below).
5. Parses the TLE/JSON body and returns typed data.

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
  `/api/refresh`, `scheduled()`, and the staleness clamp.
- `cf/src/types.ts` — update `Env`; trim D1 row types; keep `OmmRecord`,
  `PredictionConfig`, `PassResult`, `PredictionResult`, `DEFAULT_CONFIG`; add
  `TleLines`.
- `cf/src/tle-parse.ts` — shrink; keep only OMM helpers still needed for the
  `format=tle`-unavailable (NORAD > 99,999) path, if we keep that path.
- `cf/wrangler.toml` — remove D1 + cron.
- `cf/package.json` — remove `db:migrate*` and `seed` scripts.

**Unchanged:** `cf/src/predict.ts`, `cf/src/solar.ts`, `cf/public/index.html`.

## Error handling

- Upstream non-200 → map to Worker HTTP status: 404 from API → `404 NORAD not
  found`; 401/403 → `502` with a "data source auth failed" message (do not leak
  the key); other 5xx/network → `502 upstream unavailable`.
- Missing/empty TLE lines for NORAD > 99,999 (no `format=tle`) → `501 OMM-only
  records not yet supported` (preserves current behavior).
- `norad_id` missing/invalid → `400` (unchanged).

## Testing

- **Unit:** `api-client` with a mocked `fetch` — URL construction (incl.
  `epoch` param and `X-Api-Key` header), cache hit vs. miss, TLE/JSON parsing,
  and error-status mapping. `cacheTtlSeconds` returns expected buckets.
- **Prediction parity (guard):** for a known satellite (e.g. ISS 25544) with a
  fixed TLE, `runPrediction` output is unchanged vs. the pre-migration path —
  confirms only the *source* of the TLE changed, not the math.
- **Manual/E2E:** `wrangler dev` with `.dev.vars` key set; exercise all three
  routes and confirm Cache API hits on repeat (via `cf-cache-status` or logs).

## Out of scope

- Propagating OMM-only records (NORAD > 99,999) through `satellite.js` —
  pre-existing gap, unchanged.
- Any change to the legacy Python stack or `cf/public/index.html`.
