import { Hono } from "hono";
import { cors } from "hono/cors";
import * as satellite from "satellite.js";
import { healthCheck, listSatellites, getLatestTle } from "./db";
import { runPrediction, utcOffsetFromLon } from "./predict";
import { parseOmmRecord } from "./tle-parse";
import { refresh } from "./seed";
import type { Env, OmmRecord } from "./types";
import { DEFAULT_CONFIG } from "./types";

const app = new Hono<{ Bindings: Env }>();

app.use("/api/*", cors());

// --- Health ---
app.get("/api/health", async (c) => {
  const result = await healthCheck(c.env.DB);
  return c.json(result);
});

// --- Satellite search ---
app.get("/api/satellites", async (c) => {
  const q = c.req.query("q") ?? "";
  const limit = Math.min(parseInt(c.req.query("limit") ?? "50", 10), 500);
  const items = await listSatellites(c.env.DB, q, limit);
  return c.json({ items });
});

// --- Latest TLE ---
app.get("/api/tles/latest/:norad_id", async (c) => {
  const noradId = parseInt(c.req.param("norad_id"), 10);
  const rec = await getLatestTle(c.env.DB, noradId);
  if (!rec) return c.json({ error: "NORAD not found" }, 404);
  return c.json(rec);
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

  const rec = await getLatestTle(c.env.DB, noradId);
  if (!rec) return c.json({ error: "NORAD not found" }, 404);

  // Build satrec from TLE lines or OMM
  let satrec: satellite.SatRec;
  if (rec.line1 && rec.line2) {
    satrec = satellite.twoline2satrec(rec.line1, rec.line2);
  } else if (rec.omm_json) {
    // OMM-only path (NORAD > 339999)
    const omm: OmmRecord = JSON.parse(rec.omm_json);
    const parsed = parseOmmRecord(omm);
    // Build satrec from OMM elements using satellite.js
    // satellite.js doesn't have sgp4init directly, so we need TLE lines
    // For OMM-only records, we'd need to synthesize TLE or use a different approach
    // For now, return an error for OMM-only records
    return c.json({ error: "OMM-only records not yet supported in JS engine" }, 501);
  } else {
    return c.json({ error: "No TLE data available" }, 404);
  }

  // Clamp start date to within 7 days of TLE epoch
  let requestedDate = startDate;
  if (rec.epoch_utc) {
    const tleEpoch = new Date(rec.epoch_utc.replace("Z", "+00:00"));
    const requested = new Date(requestedDate + "T00:00:00Z");
    const sevenDaysLater = new Date(tleEpoch.getTime() + 7 * 86400000);
    if (requested > sevenDaysLater) {
      requestedDate = tleEpoch.toISOString().slice(0, 10);
    }
  }

  const cfg = {
    ...DEFAULT_CONFIG,
    swathKm,
    maxOffnadirDeg,
  };

  const tzOffset = utcOffsetFromLon(targetLon);
  const result = runPrediction(satrec, requestedDate, targetLat, targetLon, predictDays, cfg, tzOffset);

  // Fetch satellite name
  const satRow = await c.env.DB.prepare("SELECT name FROM satellites WHERE norad_id = ?").bind(noradId).first<{ name: string }>();

  const response: Record<string, any> = {
    norad_id: noradId,
    name: satRow?.name ?? "",
    target: { lat: targetLat, lon: targetLon },
    tle: { line1: rec.line1, line2: rec.line2 },
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

// --- Manual refresh trigger ---
app.post("/api/refresh", async (c) => {
  const result = await refresh(c.env.DB);
  return c.json({ ok: true, ...result });
});

// --- Cron trigger handler ---
export default {
  fetch: app.fetch,
  async scheduled(event: ScheduledEvent, env: Env, ctx: ExecutionContext) {
    ctx.waitUntil(
      refresh(env.DB).then((r) => {
        console.log(`Cron refresh: ${r.tles} TLEs, ${r.satellites} satellites`);
      })
    );
  },
};
