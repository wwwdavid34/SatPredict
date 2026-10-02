import * as satellite from "satellite.js";
import { solarElevation } from "./solar";
import type { PredictionConfig, PredictionResult, PassResult, DEFAULT_CONFIG } from "./types";

// Constants
const PI = Math.PI;
const TWOPI = 2 * PI;
const DEG2RAD = PI / 180.0;
const RAD2DEG = 180.0 / PI;
const EARTH_R = 6378.137; // km (WGS84 semi-major axis)
const EARTH_B = 6356.7523142; // km (WGS84 semi-minor axis)
const MPD = 24 * 60; // minutes per day
const SPD = 86400; // seconds per day
const KM_PER_DEG_LAT = 111.0;

// ---------- Vector / coordinate helpers ----------

interface Vec3 {
  x: number;
  y: number;
  z: number;
}

interface GeoPos {
  x: number; // longitude (deg)
  y: number; // latitude (deg)
  z: number; // altitude (km or m depending on context)
}

function getVec(p1: Vec3, p2: Vec3): Vec3 {
  const v = { x: p1.x - p2.x, y: p1.y - p2.y, z: p1.z - p2.z };
  const n = Math.sqrt(v.x * v.x + v.y * v.y + v.z * v.z);
  return { x: v.x / n, y: v.y / n, z: v.z / n };
}

function getAng(v1: Vec3, v2: Vec3): number {
  const dot = v1.x * v2.x + v1.y * v2.y + v1.z * v2.z;
  const mag1 = Math.sqrt(v1.x ** 2 + v1.y ** 2 + v1.z ** 2);
  const mag2 = Math.sqrt(v2.x ** 2 + v2.y ** 2 + v2.z ** 2);
  let cosA = dot / (mag1 * mag2);
  // Clamp for numerical safety
  cosA = Math.max(-1, Math.min(1, cosA));
  return Math.acos(cosA);
}

function gstime(jd: number): number {
  const tut1 = (jd - 2451545.0) / 36525.0;
  let temp =
    -6.2e-6 * tut1 * tut1 * tut1 +
    0.093104 * tut1 * tut1 +
    (876600.0 * 3600 + 8640184.812866) * tut1 +
    67310.54841;
  temp = ((temp * DEG2RAD) / 240.0) % TWOPI;
  if (temp < 0.0) temp += TWOPI;
  return temp;
}

function geo2ecf(lon: number, lat: number, alt: number): Vec3 {
  // lon, lat in radians; alt in km
  const a = EARTH_R;
  const b = EARTH_B;
  const f = (a - b) / a;
  const e2 = 2 * f - f * f;
  const normal = a / Math.sqrt(1 - e2 * Math.sin(lat) * Math.sin(lat));
  return {
    x: (normal + alt) * Math.cos(lat) * Math.cos(lon),
    y: (normal + alt) * Math.cos(lat) * Math.sin(lon),
    z: (normal * (1 - e2) + alt) * Math.sin(lat),
  };
}

function ecf2eci(ecf: Vec3, gmst: number): Vec3 {
  return {
    x: ecf.x * Math.cos(gmst) - ecf.y * Math.sin(gmst),
    y: ecf.x * Math.sin(gmst) + ecf.y * Math.cos(gmst),
    z: ecf.z,
  };
}

function geo2eci(geoPos: GeoPos, jd: number): Vec3 {
  const gmst = gstime(jd);
  const ecf = geo2ecf(geoPos.x * DEG2RAD, geoPos.y * DEG2RAD, geoPos.z);
  return ecf2eci(ecf, gmst);
}

function eci2geo(eci: Vec3, jd: number): GeoPos {
  const gmst = gstime(jd);
  const a = EARTH_R;
  const b = EARTH_B;
  const f = (a - b) / a;
  const e2 = 2 * f - f * f;
  const R = Math.sqrt(eci.x * eci.x + eci.y * eci.y);
  let longitude = Math.atan2(eci.y, eci.x) - gmst;
  let latitude = Math.atan2(eci.z, R);

  // Iterative latitude refinement
  let C = 0;
  for (let k = 0; k < 20; k++) {
    C = 1 / Math.sqrt(1 - e2 * Math.sin(latitude) * Math.sin(latitude));
    latitude = Math.atan2(eci.z + a * C * e2 * Math.sin(latitude), R);
  }
  const height = R / Math.cos(latitude) - a * C;

  longitude *= RAD2DEG;
  latitude *= RAD2DEG;
  if (longitude < -180) longitude += 360;
  if (longitude > 180) longitude -= 360;

  return { x: longitude, y: latitude, z: height };
}

/** Vincenty distance between two geo points (km). */
function getDis(c1: GeoPos, c2: GeoPos): number {
  if (c1.x === c2.x && c1.y === c2.y) return 0;

  const phi1 = c1.y * DEG2RAD;
  const lembda1 = c1.x * DEG2RAD;
  const phi2 = c2.y * DEG2RAD;
  const lembda2 = c2.x * DEG2RAD;

  if (Math.abs(phi2 - phi1) < 1e-8 && Math.abs(lembda2 - lembda1) < 1e-8) return 0;

  const f = 1.0 / 298.257223563;
  const a = EARTH_R * 1000; // meters
  const b = a * (1.0 - f);
  const U1 = Math.atan((1 - f) * Math.tan(phi1));
  const U2 = Math.atan((1 - f) * Math.tan(phi2));
  const omega = lembda2 - lembda1;

  let lembda = omega;
  let lastLembda = -4000000.0;
  let sinSigma = 0,
    cosSigma = 0,
    sigma = 0,
    sinAlpha = 0,
    alpha = 0,
    cos2sigmaM = 0,
    C = 0;
  let cnt = 0;

  while (lastLembda < -3000000.0 || (lembda !== 0 && Math.abs((lastLembda - lembda) / lembda) > 1e-9)) {
    cnt++;
    const sqrSinSigma =
      Math.cos(U2) * Math.sin(lembda) * (Math.cos(U2) * Math.sin(lembda)) +
      (Math.cos(U1) * Math.sin(U2) - Math.sin(U1) * Math.cos(U2) * Math.cos(lembda)) ** 2;

    sinSigma = Math.sqrt(sqrSinSigma);
    cosSigma = Math.sin(U1) * Math.sin(U2) + Math.cos(U1) * Math.cos(U2) * Math.cos(lembda);
    sigma = Math.atan2(sinSigma, cosSigma);
    sinAlpha = (Math.cos(U1) * Math.cos(U2) * Math.sin(lembda)) / Math.sin(sigma);
    alpha = Math.asin(Math.max(-1, Math.min(1, sinAlpha)));
    cos2sigmaM = Math.cos(sigma) - (2 * Math.sin(U1) * Math.sin(U2)) / Math.cos(alpha) ** 2;
    C = (f / 16) * Math.cos(alpha) ** 2 * (4 + f * (4 - 3 * Math.cos(alpha) ** 2));
    lastLembda = lembda;
    lembda =
      omega +
      (1 - C) *
        f *
        Math.sin(alpha) *
        (sigma + C * Math.sin(sigma) * (cos2sigmaM + C * Math.cos(sigma) * (-1 + 2 * cos2sigmaM ** 2)));

    if (cnt > 100) break;
  }

  const u2 = Math.cos(alpha) ** 2 * ((a * a - b * b) / (b * b));
  const A = 1 + (u2 / 16384) * (4096 + u2 * (-768 + u2 * (320 - 175 * u2)));
  const B = (u2 / 1024) * (256 + u2 * (-128 + u2 * (74 - 47 * u2)));
  const deltaSigma =
    B *
    sinSigma *
    (cos2sigmaM +
      (B / 4) *
        (cosSigma * (-1 + 2 * cos2sigmaM ** 2) -
          (B / 6) *
            cos2sigmaM *
            (-3 + 4 * sinSigma ** 2) *
            (-3 + 4 * cos2sigmaM ** 2)));

  return (b * A * (sigma - deltaSigma)) / 1000; // km
}

function getAzimuthEllipsoid(p1: GeoPos, p2: GeoPos): number {
  const phi1 = p1.y * DEG2RAD;
  const phi2 = p2.y * DEG2RAD;
  const L1 = p1.x * DEG2RAD;
  const L2 = p2.x * DEG2RAD;
  const f = 1 / 298.257223563;
  const L = L2 - L1;
  const oneme2 = (1 - f) * (1 - f);

  let alpha: number;
  if (phi1 === 0) {
    alpha = Math.atan(Math.sin(L) / oneme2 / Math.tan(phi2));
  } else {
    const e2 = f * (2 - f);
    const A1 = (oneme2 * Math.tan(phi2)) / Math.tan(phi1);
    const A2 =
      e2 *
      Math.sqrt(
        (1 + oneme2 * Math.tan(phi2) * Math.tan(phi2)) / (1 + oneme2 * Math.tan(phi1) * Math.tan(phi1))
      );
    const A = A1 + A2;
    alpha = Math.atan(Math.sin(L) / ((A - Math.cos(L)) * Math.sin(phi1)));
  }

  if (p2.y < p1.y) {
    alpha = p2.x > p1.x ? alpha + PI : alpha - PI;
  }
  return alpha;
}

// ---------- Julian date helpers ----------

function jday(yr: number, mon: number, day: number, hr: number, min: number, sec: number): number {
  return (
    367.0 * yr -
    Math.floor(7 * (yr + Math.floor((mon + 9) / 12.0)) * 0.25) +
    Math.floor((275 * mon) / 9.0) +
    day +
    1721013.5 +
    ((sec / 60.0 + min) / 60.0 + hr) / 24.0
  );
}

function dateToJd(dt: Date): number {
  return jday(
    dt.getUTCFullYear(),
    dt.getUTCMonth() + 1,
    dt.getUTCDate(),
    dt.getUTCHours(),
    dt.getUTCMinutes(),
    dt.getUTCSeconds() + dt.getUTCMilliseconds() / 1000
  );
}

function jdToDate(jd: number): Date {
  // Convert Julian date back to calendar date
  const z = Math.floor(jd + 0.5);
  const f = jd + 0.5 - z;
  let a = z;
  if (z >= 2299161) {
    const alpha = Math.floor((z - 1867216.25) / 36524.25);
    a = z + 1 + alpha - Math.floor(alpha / 4);
  }
  const b = a + 1524;
  const c = Math.floor((b - 122.1) / 365.25);
  const d = Math.floor(365.25 * c);
  const e = Math.floor((b - d) / 30.6001);
  const day = b - d - Math.floor(30.6001 * e);
  const mon = e < 14 ? e - 1 : e - 13;
  const yr = mon > 2 ? c - 4716 : c - 4715;
  const totalHours = f * 24;
  const hr = Math.floor(totalHours);
  const totalMin = (totalHours - hr) * 60;
  const min = Math.floor(totalMin);
  const totalSec = (totalMin - min) * 60;
  const sec = Math.floor(totalSec);
  const ms = Math.round((totalSec - sec) * 1000);
  return new Date(Date.UTC(yr, mon - 1, day, hr, min, sec, ms));
}

function formatUtc(dt: Date): string {
  const y = dt.getUTCFullYear();
  const m = String(dt.getUTCMonth() + 1).padStart(2, "0");
  const d = String(dt.getUTCDate()).padStart(2, "0");
  const h = String(dt.getUTCHours()).padStart(2, "0");
  const mi = String(dt.getUTCMinutes()).padStart(2, "0");
  const s = String(dt.getUTCSeconds()).padStart(2, "0");
  return `${y}-${m}-${d} ${h}:${mi}:${s}`;
}

// ---------- Off-nadir geometry ----------

function offnadirToGroundKm(offnadirDeg: number, satAltKm: number): number {
  const theta = offnadirDeg * DEG2RAD;
  const R = EARTH_R;
  const sinVal = ((R + satAltKm) / R) * Math.sin(theta);
  if (sinVal >= 1.0) {
    return R * Math.acos(R / (R + satAltKm));
  }
  const alpha = Math.asin(sinVal) - theta;
  return R * alpha;
}

// ---------- Main prediction engine ----------

interface PropResult {
  satLat: number;
  satLon: number;
  satAlt: number;
  satVelX: number;
  satVelY: number;
  satVelZ: number;
  scanAngle: number;
  distance: number;
  bearing: number;
}

function propagateOnce(
  satrec: satellite.SatRec,
  jd: number,
  obsGeo: GeoPos
): PropResult {
  const dtMinutes = (jd - satrec.jdsatepoch) * MPD;
  const pv = satellite.sgp4(satrec, dtMinutes);
  if (pv.position === false || pv.velocity === false) {
    throw new Error("SGP4 propagation failed");
  }
  const pos = pv.position as satellite.EciVec3<number>;
  const vel = pv.velocity as satellite.EciVec3<number>;

  const satEci: Vec3 = { x: pos.x, y: pos.y, z: pos.z };
  const satVel: Vec3 = { x: vel.x, y: vel.y, z: vel.z };
  const satGeo = eci2geo(satEci, jd);
  const obsEci = geo2eci(obsGeo, jd);

  // Surface distance (spherical)
  const ang = getAng(obsEci, satEci);
  const surfaceDistance = ang * EARTH_R;

  // Scan angle
  const dx = satEci.x - obsEci.x;
  const dy = satEci.y - obsEci.y;
  const dz = satEci.z - obsEci.z;
  const slant = Math.sqrt(dx * dx + dy * dy + dz * dz);
  const alpha = getAng(obsEci, satEci);
  const scanAngle = Math.asin(EARTH_R * Math.sin(alpha) / slant) * RAD2DEG;

  // Bearing (angle between scan vector and velocity)
  const scn = getVec(obsEci, satEci);
  const bearing = getAng(scn, satVel) * RAD2DEG;

  return {
    satLat: satGeo.y,
    satLon: satGeo.x,
    satAlt: satGeo.z,
    satVelX: satVel.x,
    satVelY: satVel.y,
    satVelZ: satVel.z,
    scanAngle,
    distance: surfaceDistance,
    bearing,
  };
}

interface ConvergeResult {
  satLat: number;
  satLon: number;
  satAlt: number;
  satVelZ: number;
  scanAngle: number;
  distance: number;
  bearing: number;
  timeEndUTC: number; // JD
  timeIniUTC: number; // JD
  exitReason: string;
  error: boolean;
}

function predict(
  satrec: satellite.SatRec,
  startJd: number,
  obsGeo: GeoPos,
  cfg: PredictionConfig
): ConvergeResult {
  let bearingDiffPrev = 100;
  let beginnerFlag = 2;
  let propCnt = 0;
  let error = false;
  const halfSwath = cfg.swathKm / 2;
  let actualEpoch = startJd;
  let tspan = cfg.coarseStepSeconds;
  let passedObsBuff = 0;
  let visibleBuff = 0;
  let passedObs = 0;
  let visible = 0;
  let exitReason = "unknown";
  let stallCount = 0;
  let prevEpoch = actualEpoch;

  let satLat = 0, satLon = 0, satAlt = 0, satVelZ = 0;
  let scanAngle = 0, surfaceDistance = 0, bearing = 0;

  while (!(passedObs && visible && Math.abs(bearingDiffPrev) < cfg.bearingPrecisionDeg) && !error) {
    propCnt++;
    if (propCnt > cfg.iterationLimit - 1) {
      error = true;
      exitReason = "max_iter";
      break;
    }

    const dtMinutes = (actualEpoch - satrec.jdsatepoch) * MPD;
    const pv = satellite.sgp4(satrec, dtMinutes);
    if (pv.position === false || pv.velocity === false) {
      error = true;
      exitReason = "sgp4_error";
      break;
    }
    const pos = pv.position as satellite.EciVec3<number>;
    const vel = pv.velocity as satellite.EciVec3<number>;
    const satEci: Vec3 = { x: pos.x, y: pos.y, z: pos.z };
    const satVel: Vec3 = { x: vel.x, y: vel.y, z: vel.z };
    const satGeo = eci2geo(satEci, actualEpoch);
    const obsEci = geo2eci(obsGeo, actualEpoch);

    satLat = satGeo.y;
    satLon = satGeo.x;
    satAlt = satGeo.z;
    satVelZ = satVel.z;

    const scn = getVec(obsEci, satEci);
    const bearingRaw = getAng(scn, satVel) * RAD2DEG;
    bearing = satGeo.x > obsGeo.x ? -bearingRaw : bearingRaw;

    const bearingDiff = Math.abs(bearing) - 90;

    if (!isFinite(bearingDiff) || !isFinite(satGeo.x) || !isFinite(satGeo.y)) {
      error = true;
      exitReason = "nan_state";
      break;
    }

    // Check if propagation passed the observer
    passedObs = 0;
    if (bearingDiff * bearingDiffPrev < 0 && !beginnerFlag) {
      passedObs = 1;
    }

    beginnerFlag = Math.max(0, beginnerFlag - 1);
    bearingDiffPrev = bearingDiff;

    // Spherical distance
    const ang = getAng(obsEci, satEci);
    surfaceDistance = ang * EARTH_R;

    if (!isFinite(surfaceDistance)) {
      error = true;
      exitReason = "nan_state";
      break;
    }

    visible = surfaceDistance < halfSwath ? 1 : 0;

    actualEpoch += tspan / SPD;

    if (!passedObsBuff && passedObs && visibleBuff && !visible) {
      visible = 1;
    }

    passedObsBuff = passedObs;
    visibleBuff = visible;

    if (passedObs && visible) {
      tspan = tspan / -20.0;
      if (Math.abs(tspan) < cfg.minStepSeconds) {
        exitReason = "min_step";
        break;
      }
    }

    // Stall watchdog
    if (Math.abs(actualEpoch - prevEpoch) < (cfg.minStepSeconds / SPD) * 0.1) {
      stallCount++;
    } else {
      stallCount = 0;
    }
    prevEpoch = actualEpoch;
    if (stallCount >= cfg.maxStallIterations) {
      error = true;
      exitReason = "stalled";
      break;
    }
  }

  if (!error && exitReason === "unknown") exitReason = "converged";

  // Final scan angle
  const obsEci = geo2eci(obsGeo, actualEpoch);
  const dtMinFinal = (actualEpoch - satrec.jdsatepoch) * MPD;
  const pvFinal = satellite.sgp4(satrec, dtMinFinal);
  if (pvFinal.position !== false) {
    const posFinal = pvFinal.position as satellite.EciVec3<number>;
    const satEciFinal: Vec3 = { x: posFinal.x, y: posFinal.y, z: posFinal.z };
    const dx = satEciFinal.x - obsEci.x;
    const dy = satEciFinal.y - obsEci.y;
    const dz = satEciFinal.z - obsEci.z;
    const slant = Math.sqrt(dx * dx + dy * dy + dz * dz);
    const alpha = getAng(obsEci, satEciFinal);
    scanAngle = Math.asin(EARTH_R * Math.sin(alpha) / slant) * RAD2DEG;
  }

  return {
    satLat,
    satLon,
    satAlt,
    satVelZ,
    scanAngle,
    distance: surfaceDistance,
    bearing,
    timeEndUTC: actualEpoch,
    timeIniUTC: startJd,
    exitReason,
    error,
  };
}

// ---------- Public API ----------

export function checkReachability(
  satrec: satellite.SatRec,
  targetLat: number,
  maxOffnadirDeg: number
): PredictionResult | null {
  const inclinationDeg = satrec.inclo * RAD2DEG;
  const apogeeAltKm = (satrec as any).alta * EARTH_R;
  const marginKm = offnadirToGroundKm(maxOffnadirDeg, apogeeAltKm);
  const marginDeg = marginKm / KM_PER_DEG_LAT;
  const maxLatDeg = inclinationDeg + marginDeg;

  if (Math.abs(targetLat) > maxLatDeg) {
    return {
      passes: {},
      reachable: false,
      max_latitude_deg: Math.round(maxLatDeg * 100) / 100,
      inclination_deg: Math.round(inclinationDeg * 100) / 100,
      offnadir_margin_deg: Math.round(marginDeg * 100) / 100,
      apogee_alt_km: Math.round(apogeeAltKm * 10) / 10,
      reason: `Target latitude ${targetLat.toFixed(1)}\u00b0 is beyond the satellite's maximum coverage latitude of \u00b1${maxLatDeg.toFixed(1)}\u00b0. This satellite can never observe this target.`,
    };
  }
  return null;
}

function geoPredict(
  satrec: satellite.SatRec,
  startDate: string,
  targetLat: number,
  targetLon: number,
  predictDays: number,
  cfg: PredictionConfig,
  timeZoneHours: number
): PredictionResult {
  const obsGeo: GeoPos = { x: targetLon, y: targetLat, z: 0 };
  const startDt = new Date(startDate + "T00:00:00Z");
  const jd = dateToJd(startDt);
  const inclinationDeg = satrec.inclo * RAD2DEG;
  const apogeeAltKm = (satrec as any).alta * EARTH_R;

  // Propagate once to get sub-satellite point
  const dtMinutes = (jd - satrec.jdsatepoch) * MPD;
  const pv = satellite.sgp4(satrec, dtMinutes);
  if (pv.position === false) {
    return {
      passes: {},
      reachable: false,
      reason: "SGP4 propagation failed for this satellite.",
    };
  }
  const pos = pv.position as satellite.EciVec3<number>;
  const satEci: Vec3 = { x: pos.x, y: pos.y, z: pos.z };
  const satGeo = eci2geo(satEci, jd);
  const obsEci = geo2eci(obsGeo, jd);

  // Distance and scan angle
  const ang = getAng(obsEci, satEci);
  const surfaceDistance = ang * EARTH_R;
  const dx = satEci.x - obsEci.x;
  const dy = satEci.y - obsEci.y;
  const dz = satEci.z - obsEci.z;
  const slant = Math.sqrt(dx * dx + dy * dy + dz * dz);
  const scanAngle = Math.asin(EARTH_R * Math.sin(ang) / slant) * RAD2DEG;

  const halfSwath = cfg.swathKm / 2;
  const inSwath = surfaceDistance <= halfSwath && scanAngle <= cfg.maxOffnadirDeg;

  if (!inSwath) {
    return {
      passes: {},
      reachable: true,
      max_latitude_deg: Math.round((inclinationDeg + offnadirToGroundKm(cfg.maxOffnadirDeg, apogeeAltKm) / KM_PER_DEG_LAT) * 100) / 100,
      inclination_deg: Math.round(inclinationDeg * 100) / 100,
      apogee_alt_km: Math.round(apogeeAltKm * 10) / 10,
      reason: `Geostationary satellite is ${surfaceDistance.toFixed(0)} km from target (swath: ${cfg.swathKm} km). Sub-satellite point: ${satGeo.y.toFixed(1)}°, ${satGeo.x.toFixed(1)}°.`,
    };
  }

  // GEO satellite is always in view — generate one "pass" per day
  const passes: Record<string, PassResult> = {};
  for (let d = 0; d < predictDays; d++) {
    const dayDt = new Date(startDt.getTime() + d * 86400000 + 12 * 3600000); // noon UTC
    const utcStr = formatUtc(dayDt);
    const dayJd = dateToJd(dayDt);
    const locJd = dayJd + timeZoneHours / 24;
    const locDt = jdToDate(locJd);
    const sunElev = solarElevation(utcStr, targetLat, targetLon);

    passes[String(d + 1)] = {
      id: d + 1,
      satLat: satGeo.y,
      satLon: satGeo.x,
      satAlt: satGeo.z,
      scanAngle,
      distance: surfaceDistance,
      bearing: 0,
      timeEndUTC: utcStr,
      timeEndLOC: formatUtc(locDt) + `(${timeZoneHours})`,
      timeEndUTC_J: dayJd,
      timeEndLOC_J: locJd,
      timeIniUTC_J: dayJd,
      exitReason: "geo_stationary",
      dayNight: sunElev > 0 ? 1 : 0,
      ascending: 0,
      solarElevation: Math.round(sunElev * 10) / 10,
      sensor_model: "pushbroom",
      observable: true,
    };
  }

  return {
    passes,
    reachable: true,
    max_latitude_deg: Math.round((inclinationDeg + offnadirToGroundKm(cfg.maxOffnadirDeg, apogeeAltKm) / KM_PER_DEG_LAT) * 100) / 100,
    inclination_deg: Math.round(inclinationDeg * 100) / 100,
    apogee_alt_km: Math.round(apogeeAltKm * 10) / 10,
    reason: "Geostationary satellite — continuously in view of target.",
  };
}

export function runPrediction(
  satrec: satellite.SatRec,
  startDate: string, // ISO date "YYYY-MM-DD"
  targetLat: number,
  targetLon: number,
  predictDays: number,
  cfg: PredictionConfig,
  timeZoneHours: number
): PredictionResult {
  // Reachability guard
  const unreachable = checkReachability(satrec, targetLat, cfg.maxOffnadirDeg);
  if (unreachable) return unreachable;

  // GEO guard: mean motion ~1 rev/day means geostationary/geosynchronous.
  // The convergence loop can't handle near-stationary satellites — instead,
  // do a single propagation and report whether the target is within swath.
  const meanMotionRevDay = satrec.no * (MPD / (2 * Math.PI)); // rad/min → rev/day
  if (meanMotionRevDay > 0.9 && meanMotionRevDay < 1.1) {
    return geoPredict(satrec, startDate, targetLat, targetLon, predictDays, cfg, timeZoneHours);
  }

  const obsGeo: GeoPos = { x: targetLon, y: targetLat, z: 0 };
  const startDt = new Date(startDate + "T00:00:00Z");
  let startJd = dateToJd(startDt);

  const pdaysMs = predictDays * 86400000;
  let elapsed = 0;
  let cnt = 0;
  const rawPasses: ConvergeResult[] = [];
  let timeIniUtc = startJd;

  while (elapsed < pdaysMs) {
    cnt++;
    const out = predict(satrec, startJd, obsGeo, cfg);

    if (cnt === 1) timeIniUtc = out.timeIniUTC;

    startJd = out.timeEndUTC + 900 / 86400;

    if (out.error) continue;

    rawPasses.push(out);

    const endDt = jdToDate(out.timeEndUTC);
    const iniDt = jdToDate(timeIniUtc);
    elapsed = endDt.getTime() - iniDt.getTime();

    // Safety: break if too many iterations
    if (cnt > predictDays * 20 + 50) break;
  }

  // Filter by sensor model and compute solar elevation
  const inclinationDeg = satrec.inclo * RAD2DEG;
  const apogeeAltKm = (satrec as any).alta * EARTH_R;
  const marginKm = offnadirToGroundKm(cfg.maxOffnadirDeg, apogeeAltKm);
  const maxLatDeg = inclinationDeg + marginKm / KM_PER_DEG_LAT;

  const filtered: Record<string, PassResult> = {};
  let idx = 0;
  for (const raw of rawPasses) {
    const halfSwath = cfg.swathKm / 2;
    if (raw.distance > halfSwath || raw.scanAngle > cfg.maxOffnadirDeg) continue;

    idx++;
    const endDt = jdToDate(raw.timeEndUTC);
    const locJd = raw.timeEndUTC + timeZoneHours / 24;
    const locDt = jdToDate(locJd);
    const utcStr = formatUtc(endDt);
    const locStr = formatUtc(locDt) + `(${timeZoneHours})`;

    const sunElev = solarElevation(utcStr, targetLat, targetLon);

    filtered[String(idx)] = {
      id: idx,
      satLat: raw.satLat,
      satLon: raw.satLon,
      satAlt: raw.satAlt,
      scanAngle: raw.scanAngle,
      distance: raw.distance,
      bearing: raw.bearing,
      timeEndUTC: utcStr,
      timeEndLOC: locStr,
      timeEndUTC_J: raw.timeEndUTC,
      timeEndLOC_J: locJd,
      timeIniUTC_J: raw.timeIniUTC,
      exitReason: raw.exitReason,
      dayNight: sunElev > 0 ? 1 : 0,
      ascending: raw.satVelZ > 0 ? 1 : 0,
      solarElevation: Math.round(sunElev * 10) / 10,
      sensor_model: "pushbroom",
      observable: true,
    };
  }

  return {
    passes: filtered,
    reachable: true,
    max_latitude_deg: Math.round(maxLatDeg * 100) / 100,
    inclination_deg: Math.round(inclinationDeg * 100) / 100,
    offnadir_margin_deg: Math.round((marginKm / KM_PER_DEG_LAT) * 100) / 100,
    apogee_alt_km: Math.round(apogeeAltKm * 10) / 10,
  };
}

/** Estimate UTC offset from longitude (simple ±15° bands). */
export function utcOffsetFromLon(lon: number): number {
  return Math.round(lon / 15.0);
}
