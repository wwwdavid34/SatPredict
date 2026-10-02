import type { OmmRecord } from "./types";

const ALPHA5_MAX = 339999;

export interface ParsedOmm {
  norad_id: number;
  name: string | null;
  epoch: string;
  mean_motion: number;
  eccentricity: number;
  inclination: number;
  ra_of_asc_node: number;
  arg_of_pericenter: number;
  mean_anomaly: number;
  bstar: number;
  mean_motion_dot: number;
  mean_motion_ddot: number;
  classification: string;
  element_set_no: number;
  rev_at_epoch: number;
  ephemeris_type: number;
  object_id: string | null;
}

export function parseOmmRecord(omm: OmmRecord): ParsedOmm {
  return {
    norad_id: parseInt(omm.NORAD_CAT_ID, 10),
    name: omm.OBJECT_NAME ?? null,
    epoch: omm.EPOCH,
    mean_motion: parseFloat(omm.MEAN_MOTION),
    eccentricity: parseFloat(omm.ECCENTRICITY),
    inclination: parseFloat(omm.INCLINATION),
    ra_of_asc_node: parseFloat(omm.RA_OF_ASC_NODE),
    arg_of_pericenter: parseFloat(omm.ARG_OF_PERICENTER),
    mean_anomaly: parseFloat(omm.MEAN_ANOMALY),
    bstar: parseFloat(omm.BSTAR),
    mean_motion_dot: parseFloat(omm.MEAN_MOTION_DOT),
    mean_motion_ddot: parseFloat(omm.MEAN_MOTION_DDOT),
    classification: (omm.CLASSIFICATION_TYPE ?? "U")[0],
    element_set_no: parseInt(omm.ELEMENT_SET_NO ?? "999", 10),
    rev_at_epoch: parseInt(omm.REV_AT_EPOCH ?? "0", 10),
    ephemeris_type: parseInt(omm.EPHEMERIS_TYPE ?? "0", 10),
    object_id: omm.OBJECT_ID ?? null,
  };
}

export function epochFromOmm(epochIso: string): string {
  let clean = epochIso.replace("Z", "+00:00");
  if (!clean.includes("+") && !clean.endsWith("+00:00")) {
    clean += "+00:00";
  }
  const dt = new Date(clean);
  return dt.toISOString().replace(".000Z", "Z");
}

function tleExpFormat(value: number): string {
  if (value === 0.0) return " 00000-0";
  const sign = value < 0 ? "-" : " ";
  const av = Math.abs(value);
  const exp = Math.floor(Math.log10(av));
  const mantissa = av / Math.pow(10, exp);
  const mantissaInt = Math.round(mantissa * 1e4);
  const tleExp = exp + 1;
  const expSign = tleExp >= 0 ? "+" : "-";
  return `${sign}${String(mantissaInt).padStart(5, "0")}${expSign}${Math.abs(tleExp)}`;
}

function tleEpoch(epochIso: string): string {
  let clean = epochIso.replace("Z", "+00:00");
  if (!clean.includes("+")) clean += "+00:00";
  const dt = new Date(clean);
  const yy = dt.getUTCFullYear() % 100;
  const start = new Date(Date.UTC(dt.getUTCFullYear(), 0, 1));
  const doy = Math.floor((dt.getTime() - start.getTime()) / 86400000) + 1;
  const frac =
    (dt.getUTCHours() * 3600 + dt.getUTCMinutes() * 60 + dt.getUTCSeconds() + dt.getUTCMilliseconds() / 1000) /
    86400.0;
  const doyFrac = (doy + frac).toFixed(8).padStart(12, "0");
  return `${String(yy).padStart(2, "0")}${doyFrac}`;
}

function tleChecksum(line: string): number {
  let s = 0;
  for (let i = 0; i < 68 && i < line.length; i++) {
    const ch = line[i];
    if (ch >= "0" && ch <= "9") s += parseInt(ch, 10);
    else if (ch === "-") s += 1;
  }
  return s % 10;
}

export function ommToTleLines(omm: OmmRecord): [string, string] | null {
  const noradId = parseInt(omm.NORAD_CAT_ID, 10);
  if (noradId > ALPHA5_MAX) return null;

  const classification = (omm.CLASSIFICATION_TYPE ?? "U")[0];
  const intlDesg = (omm.OBJECT_ID ?? "").replace(/-/g, "").padEnd(8).slice(0, 8);
  const epochStr = tleEpoch(omm.EPOCH);
  const ndot = parseFloat(omm.MEAN_MOTION_DOT);
  const ndotHalf = ndot / 2.0;
  const nddot = parseFloat(omm.MEAN_MOTION_DDOT);
  const nddotSixth = nddot / 6.0;
  const bstar = parseFloat(omm.BSTAR);
  const ephType = parseInt(omm.EPHEMERIS_TYPE ?? "0", 10);
  const elsetNo = parseInt(omm.ELEMENT_SET_NO ?? "999", 10);

  // ndot field
  const ndotSign = ndotHalf < 0 ? "-" : " ";
  const ndotAbs = Math.abs(ndotHalf);
  const ndotDigits = ndotAbs.toFixed(8).slice(1); // strip leading "0"
  const ndotField = `${ndotSign}${ndotDigits}`;

  let line1 =
    `1 ${String(noradId).padStart(5, "0")}${classification} ${intlDesg} ${epochStr}` +
    ` ${ndotField} ${tleExpFormat(nddotSixth)} ${tleExpFormat(bstar)}` +
    ` ${ephType} ${String(elsetNo).padStart(4)}`;
  line1 = line1.padEnd(68).slice(0, 68);
  line1 += String(tleChecksum(line1));

  const incl = parseFloat(omm.INCLINATION);
  const raan = parseFloat(omm.RA_OF_ASC_NODE);
  const ecc = parseFloat(omm.ECCENTRICITY);
  const argp = parseFloat(omm.ARG_OF_PERICENTER);
  const ma = parseFloat(omm.MEAN_ANOMALY);
  const mm = parseFloat(omm.MEAN_MOTION);
  const rev = parseInt(omm.REV_AT_EPOCH ?? "0", 10);

  const eccStr = ecc.toFixed(7).slice(2); // drop "0."

  let line2 =
    `2 ${String(noradId).padStart(5, "0")} ${incl.toFixed(4).padStart(8)} ${raan.toFixed(4).padStart(8)} ${eccStr}` +
    ` ${argp.toFixed(4).padStart(8)} ${ma.toFixed(4).padStart(8)} ${mm.toFixed(8).padStart(11)}${String(rev).padStart(5)}`;
  line2 = line2.padEnd(68).slice(0, 68);
  line2 += String(tleChecksum(line2));

  return [line1, line2];
}
