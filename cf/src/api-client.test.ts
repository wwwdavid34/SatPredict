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

  it("maps a rejected fetch (DNS/network failure) to ApiError(502)", async () => {
    const f = vi.fn().mockRejectedValue(new TypeError("network"));
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
