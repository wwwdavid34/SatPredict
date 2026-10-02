# Orbital Data API Migration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the Cloudflare Worker's D1-backed TLE store and daily bulk-seed cron with on-demand, cached reads from the Orbital Data API, eliminating the D1 free-tier write overage.

**Architecture:** The Worker becomes a stateless proxy over `orbital-data-api.davidhsu.cc` plus the existing `satellite.js` prediction engine. GP/OMM and catalog responses are fetched per-request and de-duplicated via the Cloudflare Cache API (no D1). The SGP4 propagator is built directly from OMM elements (`omm2satrec`) using satellite.js's deep-imported `sgp4init`/`jday`, removing the TLE-text round-trip and the NORAD>99,999 limitation.

**Tech Stack:** TypeScript, Hono, Cloudflare Workers, satellite.js 5.0.0, vitest (new, for pure-function unit tests).

**Spec:** `docs/superpowers/specs/2026-09-24-orbital-api-migration-design.md`

## Global Constraints

- API base URL: `https://orbital-data-api.davidhsu.cc/api/v1` (verbatim).
- Auth: header `X-Api-Key: <env.ORBITAL_API_KEY>` on `/gp/*` and `/catalog`. `X-Api-Key` must NEVER appear in source or `wrangler.toml`; it is a Worker secret, local dev via `cf/.dev.vars` (git-ignored).
- OMM JSON from this API uses **numeric** fields (e.g. `"MEAN_MOTION": 15.49215603`, `"NORAD_CAT_ID": 25544`) and **UPPERCASE** names (`NORAD_CAT_ID`, `OBJECT_NAME`, `EPOCH`, `INCLINATION`, …). `EPOCH` is an ISO string, sometimes without a `Z` suffix (e.g. `"2026-05-14T15:36:11.376288"` and `"2026-08-31T20:28:48.860256Z"`).
- Catalog list controls page size with `per_page` (NOT `limit`); do not follow the `pagination.next` URL (it leaks the raw API Gateway origin).
- satellite.js is pinned exactly in `package.json` (deep imports rely on its internal file layout): `"satellite.js": "5.0.0"`.
- All paths below are relative to repo root; the Worker lives under `cf/`.
- Do not modify `cf/src/predict.ts`, `cf/src/solar.ts`, or `cf/public/index.html`.

---

### Task 1: Test harness + `omm2satrec`

Build the OMM→satrec converter first; it is the correctness-critical core and everything else can be tested with mocks.

**Files:**
- Modify: `cf/package.json` (add vitest + test script; pin satellite.js)
- Create: `cf/vitest.config.ts`
- Modify: `cf/src/tle-parse.ts` (add `omm2satrec`)
- Create: `cf/src/omm2satrec.test.ts`

**Interfaces:**
- Consumes: satellite.js `sgp4init` (default export at `satellite.js/lib/propagation/sgp4init`), `jday` (named export at `satellite.js/lib/ext`), `sgp4`/`twoline2satrec` (package root).
- Produces: `export function omm2satrec(omm: ApiOmm): satellite.SatRec` and `export interface ApiOmm` in `cf/src/tle-parse.ts`.

- [ ] **Step 1: Add vitest to package.json**

Edit `cf/package.json` — pin satellite.js and add vitest. Resulting `dependencies`/`devDependencies`/`scripts`:

```json
{
  "scripts": {
    "dev": "wrangler dev",
    "deploy": "wrangler deploy",
    "test": "vitest run",
    "test:watch": "vitest"
  },
  "dependencies": {
    "hono": "^4.7.0",
    "satellite.js": "5.0.0"
  },
  "devDependencies": {
    "@cloudflare/workers-types": "^4.20250109.0",
    "typescript": "^5.7.0",
    "wrangler": "^4.0.0",
    "vitest": "^2.1.0"
  }
}
```

Then run `cd cf && npm install`.

- [ ] **Step 2: Create vitest config**

Create `cf/vitest.config.ts`:

```ts
import { defineConfig } from "vitest/config";

export default defineConfig({
  test: {
    environment: "node",
    include: ["src/**/*.test.ts"],
  },
});
```

- [ ] **Step 3: Write the failing parity test**

Create `cf/src/omm2satrec.test.ts`. The test proves `omm2satrec` produces the same propagated state as the known-good `twoline2satrec` path for ISS, and that it works for the OMM's numeric/uppercase shape.

```ts
import { describe, it, expect } from "vitest";
import * as satellite from "satellite.js";
import { omm2satrec, type ApiOmm } from "./tle-parse";

// Real ISS OMM captured from the API (numeric fields, uppercase names).
const ISS_OMM: ApiOmm = {
  OBJECT_NAME: "ISS (ZARYA)",
  OBJECT_ID: "1998-067A",
  NORAD_CAT_ID: 25544,
  EPOCH: "2026-05-14T15:36:11.376288",
  MEAN_MOTION: 15.49215603,
  ECCENTRICITY: 0.00075141,
  INCLINATION: 51.6311,
  RA_OF_ASC_NODE: 106.1165,
  ARG_OF_PERICENTER: 58.4526,
  MEAN_ANOMALY: 301.7195,
  BSTAR: 9.5926049e-5,
  MEAN_MOTION_DOT: 4.878e-5,
  MEAN_MOTION_DDOT: 0.0,
  REV_AT_EPOCH: 56655,
  CLASSIFICATION_TYPE: "U",
  ELEMENT_SET_NO: 999,
  OBJECT_TYPE: "PAYLOAD",
};

describe("omm2satrec", () => {
  it("matches twoline2satrec propagation for the equivalent TLE", () => {
    // Equivalent TLE for the same ISS element set.
    const l1 = "1 25544U 98067A   26134.65013167  .00004878  00000-0  95926-4 0  9995";
    const l2 = "2 25544  51.6311 106.1165 0007514  58.4526 301.7195 15.49215603566556";
    const fromTle = satellite.twoline2satrec(l1, l2);
    const fromOmm = omm2satrec(ISS_OMM);

    expect(fromOmm.error).toBe(0);
    // jdsatepoch must match to sub-second (the conversions share jday).
    expect(fromOmm.jdsatepoch).toBeCloseTo(fromTle.jdsatepoch, 6);

    // Propagate both 60 minutes past epoch; positions must agree closely.
    const a = satellite.sgp4(fromOmm, 60.0);
    const b = satellite.sgp4(fromTle, 60.0);
    expect(a.position).toBeTruthy();
    expect(b.position).toBeTruthy();
    if (a.position && b.position) {
      expect(a.position.x).toBeCloseTo(b.position.x, 1); // km, within ~0.1
      expect(a.position.y).toBeCloseTo(b.position.y, 1);
      expect(a.position.z).toBeCloseTo(b.position.z, 1);
    }
  });

  it("handles NORAD > 99,999 (no 5-char TLE field involved)", () => {
    const highOmm: ApiOmm = { ...ISS_OMM, NORAD_CAT_ID: 270000, OBJECT_NAME: "HIGH ID TEST" };
    const satrec = omm2satrec(highOmm);
    expect(satrec.error).toBe(0);
    const g = satellite.sgp4(satrec, 10.0);
    expect(g.position).toBeTruthy();
  });

  it("parses an EPOCH string that already has a Z suffix", () => {
    const satrec = omm2satrec({ ...ISS_OMM, EPOCH: "2026-08-31T20:28:48.860256Z" });
    expect(satrec.error).toBe(0);
    expect(Number.isFinite(satrec.jdsatepoch)).toBe(true);
  });
});
```

- [ ] **Step 4: Run the test, verify it fails**

Run: `cd cf && npx vitest run src/omm2satrec.test.ts`
Expected: FAIL — `omm2satrec`/`ApiOmm` not exported from `tle-parse`.

- [ ] **Step 5: Implement `omm2satrec` and `ApiOmm`**

Add to the top of `cf/src/tle-parse.ts` (imports) and append the new code. The deep imports:

```ts
import * as satellite from "satellite.js";
// @ts-expect-error deep import: sgp4init is not in the package's type surface
import sgp4init from "satellite.js/lib/propagation/sgp4init";
// @ts-expect-error deep import: jday is not in the package's type surface
import { jday } from "satellite.js/lib/ext";

/** OMM record as returned by orbital-data-api (numeric fields, UPPERCASE names). */
export interface ApiOmm {
  OBJECT_NAME?: string;
  OBJECT_ID?: string;
  NORAD_CAT_ID: number;
  EPOCH: string;
  MEAN_MOTION: number;
  ECCENTRICITY: number;
  INCLINATION: number;
  RA_OF_ASC_NODE: number;
  ARG_OF_PERICENTER: number;
  MEAN_ANOMALY: number;
  BSTAR: number;
  MEAN_MOTION_DOT?: number;
  MEAN_MOTION_DDOT?: number;
  REV_AT_EPOCH?: number;
  CLASSIFICATION_TYPE?: string;
  ELEMENT_SET_NO?: number;
  OBJECT_TYPE?: string;
  ORBIT_REGIME?: string;
}

const DEG2RAD = Math.PI / 180.0;
const XPDOTP = 1440.0 / (2.0 * Math.PI); // rev/day -> rad/min divisor (matches twoline2satrec)

/**
 * Build an SGP4 satrec directly from OMM mean elements, mirroring exactly what
 * satellite.js's twoline2satrec does before its sgp4init call — but with no
 * fixed-width TLE text, so NORAD IDs of any length work.
 */
export function omm2satrec(omm: ApiOmm): satellite.SatRec {
  // Normalize EPOCH to a Date; append Z if the API omitted the zone.
  const epochStr = /[Zz]|[+-]\d\d:?\d\d$/.test(omm.EPOCH) ? omm.EPOCH : omm.EPOCH + "Z";
  const d = new Date(epochStr);
  const secFrac = d.getUTCSeconds() + d.getUTCMilliseconds() / 1000;
  const jdsatepoch = jday(
    d.getUTCFullYear(),
    d.getUTCMonth() + 1,
    d.getUTCDate(),
    d.getUTCHours(),
    d.getUTCMinutes(),
    secFrac
  );

  const satrec: any = {};
  satrec.error = 0;
  satrec.satnum = String(omm.NORAD_CAT_ID); // opaque string; no length limit
  satrec.jdsatepoch = jdsatepoch;
  satrec.no = omm.MEAN_MOTION / XPDOTP; // rad/min
  satrec.ecco = omm.ECCENTRICITY;
  satrec.inclo = omm.INCLINATION * DEG2RAD;
  satrec.nodeo = omm.RA_OF_ASC_NODE * DEG2RAD;
  satrec.argpo = omm.ARG_OF_PERICENTER * DEG2RAD;
  satrec.mo = omm.MEAN_ANOMALY * DEG2RAD;
  satrec.bstar = omm.BSTAR;

  sgp4init(satrec, {
    opsmode: "i",
    satn: satrec.satnum,
    epoch: satrec.jdsatepoch - 2433281.5,
    xbstar: satrec.bstar,
    xecco: satrec.ecco,
    xargpo: satrec.argpo,
    xinclo: satrec.inclo,
    xmo: satrec.mo,
    xno: satrec.no,
    xnodeo: satrec.nodeo,
  });

  return satrec as satellite.SatRec;
}
```

Note: if the parity test reveals `sgp4init` also reads `satrec.epochyr`/`satrec.epochdays`, set them from `d` (year%100 and day-of-year+fraction) before the `sgp4init` call. The test is the arbiter.

- [ ] **Step 6: Run the test, verify it passes**

Run: `cd cf && npx vitest run src/omm2satrec.test.ts`
Expected: PASS (all three cases). If the parity case fails on position, re-check the `no` scaling and that `jdsatepoch` matches; add `epochyr`/`epochdays` if needed.

- [ ] **Step 7: Commit**

```bash
git add cf/package.json cf/package-lock.json cf/vitest.config.ts cf/src/tle-parse.ts cf/src/omm2satrec.test.ts
git commit -m "feat(cf): add omm2satrec via deep-imported sgp4init + vitest harness"
```

---

### Task 2: `cacheTtlSeconds` freshness policy

**Files:**
- Create: `cf/src/cache-policy.ts`
- Create: `cf/src/cache-policy.test.ts`

**Interfaces:**
- Produces: `export function cacheTtlSeconds(kind: "latest" | "search" | "historical", epochDate?: string): number`

- [ ] **Step 1: Write the failing test**

Create `cf/src/cache-policy.test.ts`:

```ts
import { describe, it, expect } from "vitest";
import { cacheTtlSeconds } from "./cache-policy";

describe("cacheTtlSeconds", () => {
  it("search is cached ~1h", () => {
    expect(cacheTtlSeconds("search")).toBe(3600);
  });
  it("latest is cached ~6h", () => {
    expect(cacheTtlSeconds("latest")).toBe(21600);
  });
  it("historical (clearly past epoch) is cached long", () => {
    expect(cacheTtlSeconds("historical", "2020-01-01")).toBe(2592000); // 30d
  });
  it("historical near today falls back to the latest TTL", () => {
    const today = new Date().toISOString().slice(0, 10);
    expect(cacheTtlSeconds("historical", today)).toBe(21600);
  });
});
```

- [ ] **Step 2: Run test, verify it fails**

Run: `cd cf && npx vitest run src/cache-policy.test.ts`
Expected: FAIL — module not found.

- [ ] **Step 3: Implement**

Create `cf/src/cache-policy.ts`:

```ts
const HOUR = 3600;
const DAY = 86400;

/** Cache max-age (seconds) for a given query kind. Isolated so freshness is easy to tune. */
export function cacheTtlSeconds(
  kind: "latest" | "search" | "historical",
  epochDate?: string
): number {
  if (kind === "search") return 1 * HOUR;
  if (kind === "latest") return 6 * HOUR;
  // historical: immutable if the requested date is comfortably in the past (>2 days),
  // otherwise it's effectively "current" and should refresh like latest.
  if (epochDate) {
    const reqMs = new Date(epochDate + "T00:00:00Z").getTime();
    if (Date.now() - reqMs > 2 * DAY * 1000) return 30 * DAY;
  }
  return 6 * HOUR;
}
```

- [ ] **Step 4: Run test, verify it passes**

Run: `cd cf && npx vitest run src/cache-policy.test.ts`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add cf/src/cache-policy.ts cf/src/cache-policy.test.ts
git commit -m "feat(cf): add cacheTtlSeconds freshness policy"
```

---

### Task 3: `api-client.ts`

Typed client over the Orbital Data API with Cache API de-dup. Cache access is guarded (`globalThis.caches`) so it is a no-op under node/vitest and real under Workers. `fetch` is injectable for tests.

**Files:**
- Create: `cf/src/api-client.ts`
- Create: `cf/src/api-client.test.ts`

**Interfaces:**
- Consumes: `ApiOmm` (Task 1), `cacheTtlSeconds` (Task 2), `Env` (Task 4 defines `ORBITAL_API_KEY`; for this task assume `{ ORBITAL_API_KEY: string }`).
- Produces:
  - `export interface CatalogItem { norad_id: number; name: string; object_type: string | null; }`
  - `export async function getLatestOmm(env: Env, noradId: number, fetchImpl?: typeof fetch): Promise<ApiOmm | null>`
  - `export async function getNearestOmm(env: Env, noradId: number, epochDate: string, fetchImpl?: typeof fetch): Promise<ApiOmm | null>`
  - `export async function searchCatalog(env: Env, query: string, perPage: number, fetchImpl?: typeof fetch): Promise<CatalogItem[]>`
  - `export class ApiError extends Error { constructor(public status: number, message: string) }`

- [ ] **Step 1: Write the failing tests**

Create `cf/src/api-client.test.ts`:

```ts
import { describe, it, expect, vi } from "vitest";
import { getLatestOmm, getNearestOmm, searchCatalog, ApiError } from "./api-client";

const env = { ORBITAL_API_KEY: "test-key" } as any;

function jsonResponse(body: unknown, status = 200): Response {
  return new Response(JSON.stringify(body), {
    status,
    headers: { "content-type": "application/json" },
  });
}

describe("getLatestOmm", () => {
  it("requests /gp/{id}?format=json with the API key and returns the OMM", async () => {
    const f = vi.fn().mockResolvedValue(jsonResponse({ NORAD_CAT_ID: 25544, EPOCH: "2026-05-14T15:36:11Z", MEAN_MOTION: 15.49 }));
    const omm = await getLatestOmm(env, 25544, f as any);
    expect(omm?.NORAD_CAT_ID).toBe(25544);
    const [url, opts] = f.mock.calls[0];
    expect(url).toBe("https://orbital-data-api.davidhsu.cc/api/v1/gp/25544?format=json");
    expect((opts.headers as any)["X-Api-Key"]).toBe("test-key");
  });

  it("returns null on 404", async () => {
    const f = vi.fn().mockResolvedValue(jsonResponse({ message: "not found" }, 404));
    expect(await getLatestOmm(env, 999999999, f as any)).toBeNull();
  });

  it("throws ApiError(502) on 401/403 without leaking the key", async () => {
    const f = vi.fn().mockResolvedValue(jsonResponse({ error: "INVALID_API_KEY" }, 403));
    await expect(getLatestOmm(env, 25544, f as any)).rejects.toMatchObject({ status: 502 });
  });
});

describe("getNearestOmm", () => {
  it("includes the epoch query param", async () => {
    const f = vi.fn().mockResolvedValue(jsonResponse({ NORAD_CAT_ID: 25544, EPOCH: "2026-08-31T20:28:48Z", MEAN_MOTION: 15.48 }));
    await getNearestOmm(env, 25544, "2026-09-01", f as any);
    expect(f.mock.calls[0][0]).toBe(
      "https://orbital-data-api.davidhsu.cc/api/v1/gp/25544/nearest?epoch=2026-09-01&format=json"
    );
  });
});

describe("searchCatalog", () => {
  it("maps uppercase catalog fields to CatalogItem and uses per_page", async () => {
    const f = vi.fn().mockResolvedValue(
      jsonResponse({
        data: [{ NORAD_CAT_ID: 25544, OBJECT_NAME: "ISS (ZARYA)", OBJECT_TYPE: "PAYLOAD" }],
        pagination: { total: 1 },
      })
    );
    const items = await searchCatalog(env, "ZARYA", 50, f as any);
    expect(items).toEqual([{ norad_id: 25544, name: "ISS (ZARYA)", object_type: "PAYLOAD" }]);
    expect(f.mock.calls[0][0]).toBe(
      "https://orbital-data-api.davidhsu.cc/api/v1/catalog?search=ZARYA&per_page=50"
    );
  });

  it("returns [] for an empty query", async () => {
    const f = vi.fn();
    expect(await searchCatalog(env, "", 50, f as any)).toEqual([]);
    expect(f).not.toHaveBeenCalled();
  });
});
```

- [ ] **Step 2: Run tests, verify they fail**

Run: `cd cf && npx vitest run src/api-client.test.ts`
Expected: FAIL — module not found.

- [ ] **Step 3: Implement `api-client.ts`**

Create `cf/src/api-client.ts`:

```ts
import type { ApiOmm } from "./tle-parse";
import { cacheTtlSeconds } from "./cache-policy";
import type { Env } from "./types";

const BASE = "https://orbital-data-api.davidhsu.cc/api/v1";

export class ApiError extends Error {
  constructor(public status: number, message: string) {
    super(message);
    this.name = "ApiError";
  }
}

export interface CatalogItem {
  norad_id: number;
  name: string;
  object_type: string | null;
}

/** Fetch with API key + Cache API de-dup. Cache is a no-op when `caches` is absent (node/tests). */
async function cachedFetch(
  url: string,
  env: Env,
  ttl: number,
  fetchImpl: typeof fetch
): Promise<Response> {
  const cache = (globalThis as any).caches?.default as Cache | undefined;
  const req = new Request(url, { headers: { "X-Api-Key": env.ORBITAL_API_KEY } });
  if (cache) {
    const hit = await cache.match(req);
    if (hit) return hit;
  }
  const resp = await fetchImpl(url, { headers: { "X-Api-Key": env.ORBITAL_API_KEY } });
  if (cache && resp.ok) {
    const toCache = new Response(resp.clone().body, resp);
    toCache.headers.set("Cache-Control", `max-age=${ttl}`);
    await cache.put(req, toCache);
  }
  return resp;
}

/** Map upstream HTTP status to our behavior. 404 -> null; 401/403/5xx -> ApiError(502). */
function assertOkOrNull(resp: Response): "null" | "ok" {
  if (resp.ok) return "ok";
  if (resp.status === 404) return "null";
  if (resp.status === 401 || resp.status === 403) {
    throw new ApiError(502, "data source auth failed");
  }
  throw new ApiError(502, "upstream unavailable");
}

export async function getLatestOmm(
  env: Env,
  noradId: number,
  fetchImpl: typeof fetch = fetch
): Promise<ApiOmm | null> {
  const url = `${BASE}/gp/${noradId}?format=json`;
  const resp = await cachedFetch(url, env, cacheTtlSeconds("latest"), fetchImpl);
  if (assertOkOrNull(resp) === "null") return null;
  return (await resp.json()) as ApiOmm;
}

export async function getNearestOmm(
  env: Env,
  noradId: number,
  epochDate: string,
  fetchImpl: typeof fetch = fetch
): Promise<ApiOmm | null> {
  const url = `${BASE}/gp/${noradId}/nearest?epoch=${encodeURIComponent(epochDate)}&format=json`;
  const resp = await cachedFetch(url, env, cacheTtlSeconds("historical", epochDate), fetchImpl);
  if (assertOkOrNull(resp) === "null") return null;
  return (await resp.json()) as ApiOmm;
}

export async function searchCatalog(
  env: Env,
  query: string,
  perPage: number,
  fetchImpl: typeof fetch = fetch
): Promise<CatalogItem[]> {
  if (!query) return [];
  const url = `${BASE}/catalog?search=${encodeURIComponent(query)}&per_page=${perPage}`;
  const resp = await cachedFetch(url, env, cacheTtlSeconds("search"), fetchImpl);
  if (assertOkOrNull(resp) === "null") return [];
  const body = (await resp.json()) as { data?: Array<Record<string, any>> };
  return (body.data ?? []).map((r) => ({
    norad_id: r.NORAD_CAT_ID,
    name: r.OBJECT_NAME ?? "",
    object_type: r.OBJECT_TYPE ?? null,
  }));
}
```

- [ ] **Step 4: Run tests, verify they pass**

Run: `cd cf && npx vitest run src/api-client.test.ts`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add cf/src/api-client.ts cf/src/api-client.test.ts
git commit -m "feat(cf): add api-client over Orbital Data API with Cache API de-dup"
```

---

### Task 4: Rewrite routes in `index.ts` and update `Env`

**Files:**
- Modify: `cf/src/types.ts` (Env: drop `DB`, add `ORBITAL_API_KEY`; remove D1 row types)
- Modify: `cf/src/index.ts` (rewrite 3 routes; remove `/api/refresh`, `scheduled`, staleness clamp)

**Interfaces:**
- Consumes: `getLatestOmm`, `getNearestOmm`, `searchCatalog`, `ApiError` (Task 3); `omm2satrec` (Task 1); `runPrediction`, `utcOffsetFromLon` (existing `predict.ts`); `DEFAULT_CONFIG`, `PredictionConfig` (existing `types.ts`).
- Produces: the Worker's public HTTP API (unchanged response contract for the frontend).

- [ ] **Step 1: Update `Env` and trim D1 types in `types.ts`**

In `cf/src/types.ts`, replace the `Env` interface and remove `SatelliteRow`, `TleRow`, and the string-based `OmmRecord` (superseded by `ApiOmm` in `tle-parse.ts`). Keep `SatelliteSearchResult`, `PredictionConfig`, `PassResult`, `PredictionResult`, `DEFAULT_CONFIG`.

```ts
export interface Env {
  ORBITAL_API_KEY: string;
}
```

- [ ] **Step 2: Rewrite `index.ts`**

Replace the full contents of `cf/src/index.ts` with:

```ts
import { Hono } from "hono";
import { cors } from "hono/cors";
import { getLatestOmm, getNearestOmm, searchCatalog, ApiError } from "./api-client";
import { omm2satrec } from "./tle-parse";
import { runPrediction, utcOffsetFromLon } from "./predict";
import { DEFAULT_CONFIG } from "./types";
import type { Env } from "./types";

const app = new Hono<{ Bindings: Env }>();

app.use("/api/*", cors());

app.onError((err, c) => {
  if (err instanceof ApiError) return c.json({ error: err.message }, err.status as any);
  console.error(err);
  return c.json({ error: "internal error" }, 500);
});

app.get("/api/health", (c) => c.json({ ok: true }));

// --- Satellite search ---
app.get("/api/satellites", async (c) => {
  const q = c.req.query("q") ?? "";
  const perPage = Math.min(parseInt(c.req.query("limit") ?? "50", 10), 100);
  const items = await searchCatalog(c.env, q, perPage);
  return c.json({ items });
});

// --- Latest OMM (returns raw OMM; frontend uses name/epoch) ---
app.get("/api/tles/latest/:norad_id", async (c) => {
  const noradId = parseInt(c.req.param("norad_id"), 10);
  const omm = await getLatestOmm(c.env, noradId);
  if (!omm) return c.json({ error: "NORAD not found" }, 404);
  return c.json(omm);
});

// --- Predict overpass ---
app.get("/api/predict/overpass", async (c) => {
  const noradId = parseInt(c.req.query("norad_id") ?? "0", 10);
  const targetLat = parseFloat(c.req.query("target_lat") ?? "0");
  const targetLon = parseFloat(c.req.query("target_lon") ?? "0");
  const startDate = c.req.query("start_date") ?? new Date().toISOString().slice(0, 10);
  const predictDays = parseInt(c.req.query("predict_days") ?? "1", 10);
  const swathKm = parseFloat(c.req.query("swath_km") ?? "3000");
  const maxOffnadirDeg = parseFloat(c.req.query("max_offnadir_deg") ?? "55");

  if (!noradId) return c.json({ error: "norad_id required" }, 400);

  // Fetch the element set nearest the requested date (date-accurate prediction).
  const omm = await getNearestOmm(c.env, noradId, startDate);
  if (!omm) return c.json({ error: "NORAD not found" }, 404);

  const satrec = omm2satrec(omm);

  const cfg = { ...DEFAULT_CONFIG, swathKm, maxOffnadirDeg };
  const tzOffset = utcOffsetFromLon(targetLon);
  const result = runPrediction(satrec, startDate, targetLat, targetLon, predictDays, cfg, tzOffset);

  const response: Record<string, any> = {
    norad_id: noradId,
    name: omm.OBJECT_NAME ?? "",
    target: { lat: targetLat, lon: targetLon },
    epoch_utc: omm.EPOCH,
    swath_km: cfg.swathKm,
    passes: Object.keys(result.passes)
      .sort((a, b) => parseInt(a) - parseInt(b))
      .map((k) => result.passes[k]),
    count: Object.keys(result.passes).length,
    reachable: result.reachable,
  };
  if (result.max_latitude_deg != null) response.max_latitude_deg = result.max_latitude_deg;
  if (result.inclination_deg != null) response.inclination_deg = result.inclination_deg;
  if (result.offnadir_margin_deg != null) response.offnadir_margin_deg = result.offnadir_margin_deg;
  if (result.apogee_alt_km != null) response.apogee_alt_km = result.apogee_alt_km;
  if (result.reason) response.reason = result.reason;

  return c.json(response);
});

export default { fetch: app.fetch };
```

- [ ] **Step 3: Typecheck**

Run: `cd cf && npx tsc --noEmit`
Expected: no errors. (The `@ts-expect-error` deep-import lines in `tle-parse.ts` are expected and intentional.)

- [ ] **Step 4: Run the full test suite**

Run: `cd cf && npm test`
Expected: all tests from Tasks 1–3 PASS.

- [ ] **Step 5: Commit**

```bash
git add cf/src/index.ts cf/src/types.ts
git commit -m "feat(cf): rewrite routes to use Orbital Data API; drop D1 Env/cron/refresh"
```

---

### Task 5: Remove D1 ingestion + cron config

**Files:**
- Delete: `cf/src/seed.ts`, `cf/src/db.ts`, `cf/migrations/` (entire dir)
- Modify: `cf/wrangler.toml` (remove `[[d1_databases]]` and `[triggers]`)
- Modify: `cf/package.json` (remove `db:migrate*`, `seed` scripts — already dropped in Task 1 if done then; verify none remain)
- Modify: `cf/src/tle-parse.ts` (remove now-unused OMM→TLE text helpers if nothing imports them)

**Interfaces:**
- Consumes: nothing new.
- Produces: a Worker with no D1 dependency.

- [ ] **Step 1: Delete dead modules and migrations**

```bash
cd cf && rm -f src/seed.ts src/db.ts && rm -rf migrations
```

- [ ] **Step 2: Edit `wrangler.toml`**

Remove the `[[d1_databases]]` block and the `[triggers]` block. Resulting file:

```toml
name = "satpredict"
main = "src/index.ts"
compatibility_date = "2024-12-01"
account_id = "f363e618f4b8dc5f5a3b8cb169f3ddb7"
workers_dev = true

# ORBITAL_API_KEY is a Worker secret (wrangler secret put ORBITAL_API_KEY);
# local dev reads it from cf/.dev.vars (git-ignored).

[assets]
directory = "./public"
```

- [ ] **Step 3: Remove unused TLE-text helpers from `tle-parse.ts`**

Search for any remaining imports of `parseOmmRecord`, `epochFromOmm`, `ommToTleLines`:

Run: `cd cf && grep -rn "parseOmmRecord\|epochFromOmm\|ommToTleLines" src/`
If the only matches are their definitions in `tle-parse.ts` (no importers), delete those functions and the `ParsedOmm` interface and the `ALPHA5_MAX`/`tleExpFormat`/`tleEpoch`/`tleChecksum` helpers. Keep `ApiOmm` and `omm2satrec`.

- [ ] **Step 4: Typecheck + test + verify no D1 references remain**

Run: `cd cf && npx tsc --noEmit && npm test`
Expected: PASS.
Run: `cd cf && grep -rn "D1Database\|DB\b\|miniflare\|d1_databases" src/ wrangler.toml`
Expected: no matches (or only unrelated).

- [ ] **Step 5: Commit**

```bash
git add -A cf/
git commit -m "chore(cf): remove D1 store, seeding, migrations, and cron trigger"
```

---

### Task 6: Live end-to-end verification (run by the API owner's environment)

This task is **not** automated TDD — it exercises the real Worker against the live API. Run it from an environment that can reach the validated endpoints (the API owner's).

**Files:** none (verification only).

- [ ] **Step 1: Set the local dev secret**

Confirm `cf/.dev.vars` contains `ORBITAL_API_KEY=<key>` (git-ignored). For production: `cd cf && npx wrangler secret put ORBITAL_API_KEY`.

- [ ] **Step 2: Start the Worker**

Run: `cd cf && npm run dev`
Expected: wrangler serves on `http://localhost:8787`.

- [ ] **Step 3: Exercise each route**

```bash
curl -s "http://localhost:8787/api/health"
curl -s "http://localhost:8787/api/satellites?q=ZARYA"
curl -s "http://localhost:8787/api/tles/latest/25544"
curl -s "http://localhost:8787/api/predict/overpass?norad_id=25544&target_lat=39.7&target_lon=-104.99&start_date=2026-09-01&predict_days=2"
```
Expected: health ok; search returns ISS (ZARYA) with norad 25544; latest returns an OMM; predict returns a `passes` array with `epoch_utc` near the requested `start_date` (proves `/nearest` date-accuracy).

- [ ] **Step 4: Confirm a high-NORAD prediction works**

Pick a NORAD > 99,999 that exists in the catalog (via `/api/satellites?q=...`) and call `/api/predict/overpass` for it. Expected: a valid prediction (no 501), proving the OMM-native path removed the old limitation.

- [ ] **Step 5: Confirm caching**

Repeat a prediction call twice; check wrangler logs / `cf-cache-status` for a cache hit on the second upstream request.

---

## Self-Review

**Spec coverage:**
- Remove D1 / zero writes → Tasks 4, 5. ✓
- Stateless proxy + Cache API → Task 3 (`cachedFetch`). ✓
- Native OMM→satrec via deep-imported sgp4init, isolated → Task 1. ✓
- NORAD>99,999 supported → Task 1 (high-id test), Task 6 step 4. ✓
- `/gp/nearest` for date-accurate prediction; staleness clamp deleted → Task 4 (clamp gone; `getNearestOmm` used). ✓
- Search via authed `/catalog` (`per_page`, uppercase fields) → Task 3. ✓
- `ORBITAL_API_KEY` secret, not in source → Global Constraints, Tasks 4/5/6. ✓
- Remove `/api/refresh`, `scheduled`, cron → Tasks 4, 5. ✓
- Error mapping (404→null/404; 401/403→502) → Task 3 (`assertOkOrNull`), Task 4 (`onError`). ✓
- Freshness policy isolated → Task 2. ✓
- Parity test → Task 1. ✓

**Placeholder scan:** No TBD/TODO; all steps carry concrete code and exact run commands.

**Type consistency:** `ApiOmm` (Task 1) consumed by `api-client` (Task 3) and `index.ts` (Task 4). `CatalogItem` (Task 3) shape matches `searchCatalog` test and route. `Env` (`{ ORBITAL_API_KEY }`) defined in Task 4, assumed by Task 3's signatures — consistent. `omm2satrec` returns `satellite.SatRec`, consumed by `runPrediction` whose first param is `satellite.SatRec`. ✓

Known risk flagged inline: `sgp4init` may require `satrec.epochyr`/`epochdays`; the Task 1 parity test is the arbiter and the fix is specified in Task 1 Step 5.
