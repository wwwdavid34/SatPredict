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
  const headers = { "X-Api-Key": env.ORBITAL_API_KEY };
  const req = new Request(url, { headers });
  if (cache) {
    const hit = await cache.match(req);
    if (hit) return hit;
  }
  let resp: Response;
  try {
    resp = await fetchImpl(url, { headers });
  } catch {
    throw new ApiError(502, "upstream unavailable");
  }
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
