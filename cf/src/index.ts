import { Hono } from "hono";
import { cors } from "hono/cors";
import { getLatestOmm, getNearestOmm, searchCatalog, ApiError } from "./api-client";
import { omm2satrec, apiOmmToTleLines } from "./tle-parse";
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
  if (Number.isNaN(noradId)) return c.json({ error: "invalid norad_id" }, 400);
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
    tle: apiOmmToTleLines(omm),
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
