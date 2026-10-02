import { batchUpsertSatellites, batchUpsertTles } from "./db";
import { ommToTleLines, epochFromOmm, parseOmmRecord } from "./tle-parse";
import type { OmmRecord } from "./types";

const CELESTRAK_BASE = "https://celestrak.org/NORAD/elements/gp.php";
const CELESTRAK_SATCAT = "https://celestrak.org/pub/satcat.csv";

const TLE_GROUPS = [
  "weather",
  "noaa",
  "resource",
  "stations",
  "active",
  "visual",
  "science",
];

async function fetchJson(url: string): Promise<any> {
  const resp = await fetch(url);
  if (!resp.ok) throw new Error(`Fetch failed: ${resp.status} ${url}`);
  return resp.json();
}

async function fetchText(url: string): Promise<string> {
  const resp = await fetch(url);
  if (!resp.ok) throw new Error(`Fetch failed: ${resp.status} ${url}`);
  return resp.text();
}

/** Seed TLEs from CelesTrak OMM JSON for all configured groups. */
export async function seedTles(db: D1Database): Promise<number> {
  let total = 0;

  for (const group of TLE_GROUPS) {
    try {
      const url = `${CELESTRAK_BASE}?GROUP=${group}&FORMAT=json`;
      const records: OmmRecord[] = await fetchJson(url);

      const rows: Array<{
        norad_id: number;
        line1: string | null;
        line2: string | null;
        epoch_utc: string | null;
        source: string;
        omm_json: string | null;
      }> = [];

      for (const omm of records) {
        const parsed = parseOmmRecord(omm);
        const epochUtc = epochFromOmm(parsed.epoch);
        const tlePair = ommToTleLines(omm);

        rows.push({
          norad_id: parsed.norad_id,
          line1: tlePair ? tlePair[0] : null,
          line2: tlePair ? tlePair[1] : null,
          epoch_utc: epochUtc,
          source: `celestrak:${group}`,
          omm_json: JSON.stringify(omm),
        });
      }

      await batchUpsertTles(db, rows);

      // Also upsert satellite names from OMM
      const satRows = records.map((omm) => ({
        norad_id: parseInt(omm.NORAD_CAT_ID, 10),
        name: omm.OBJECT_NAME ?? `NORAD ${omm.NORAD_CAT_ID}`,
        intl_designator: omm.OBJECT_ID ?? null,
        object_type: omm.OBJECT_TYPE ?? null,
      }));
      await batchUpsertSatellites(db, satRows);

      total += rows.length;
      console.log(`Seeded ${rows.length} TLEs from group: ${group}`);
    } catch (err) {
      console.error(`Failed to seed group ${group}:`, err);
    }
  }

  return total;
}

/** Seed satellite catalog from CelesTrak SATCAT CSV. */
export async function seedSatcat(db: D1Database): Promise<number> {
  try {
    const text = await fetchText(CELESTRAK_SATCAT);
    const lines = text.split("\n");
    if (lines.length < 2) return 0;

    // Parse CSV header
    const header = lines[0].split(",").map((h) => h.trim());
    const noradIdx = header.indexOf("NORAD_CAT_ID");
    const nameIdx = header.indexOf("OBJECT_NAME");
    const intlIdx = header.indexOf("INTLDES");
    const typeIdx = header.indexOf("OBJECT_TYPE");

    if (noradIdx < 0 || nameIdx < 0) {
      console.error("SATCAT CSV missing required columns");
      return 0;
    }

    const rows: Array<{
      norad_id: number;
      name: string;
      intl_designator: string | null;
      object_type: string | null;
    }> = [];

    for (let i = 1; i < lines.length; i++) {
      const line = lines[i].trim();
      if (!line) continue;
      const cols = parseCSVLine(line);
      const noradStr = cols[noradIdx]?.trim();
      const name = cols[nameIdx]?.trim();
      if (!noradStr || !name) continue;

      const noradId = parseInt(noradStr, 10);
      if (isNaN(noradId)) continue;

      rows.push({
        norad_id: noradId,
        name,
        intl_designator: intlIdx >= 0 ? cols[intlIdx]?.trim() || null : null,
        object_type: typeIdx >= 0 ? cols[typeIdx]?.trim() || null : null,
      });
    }

    await batchUpsertSatellites(db, rows);
    console.log(`Seeded ${rows.length} satellites from SATCAT`);
    return rows.length;
  } catch (err) {
    console.error("Failed to seed SATCAT:", err);
    return 0;
  }
}

/** Simple CSV line parser handling quoted fields. */
function parseCSVLine(line: string): string[] {
  const result: string[] = [];
  let current = "";
  let inQuotes = false;

  for (let i = 0; i < line.length; i++) {
    const ch = line[i];
    if (ch === '"') {
      inQuotes = !inQuotes;
    } else if (ch === "," && !inQuotes) {
      result.push(current);
      current = "";
    } else {
      current += ch;
    }
  }
  result.push(current);
  return result;
}

/** Full refresh: TLEs + SATCAT. */
export async function refresh(db: D1Database): Promise<{ tles: number; satellites: number }> {
  const tles = await seedTles(db);
  const satellites = await seedSatcat(db);
  return { tles, satellites };
}
