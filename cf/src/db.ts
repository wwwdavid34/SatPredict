import type { SatelliteSearchResult, TleRow } from "./types";

export async function healthCheck(db: D1Database): Promise<{ ok: boolean; satellites: number }> {
  const row = await db.prepare("SELECT COUNT(*) AS cnt FROM tle_latest").first<{ cnt: number }>();
  return { ok: true, satellites: row?.cnt ?? 0 };
}

export async function listSatellites(
  db: D1Database,
  q: string,
  limit: number
): Promise<SatelliteSearchResult[]> {
  const like = `%${q}%`;
  const rows = await db
    .prepare(
      `SELECT s.norad_id, s.name, s.object_type, t.epoch_utc
       FROM satellites s
       INNER JOIN tle_latest t ON s.norad_id = t.norad_id
       WHERE (? = '' OR CAST(s.norad_id AS TEXT) LIKE ? OR s.name LIKE ?)
       ORDER BY t.epoch_utc DESC
       LIMIT ?`
    )
    .bind(q, like, like, limit)
    .all<SatelliteSearchResult>();
  return rows.results;
}

export async function getLatestTle(db: D1Database, noradId: number): Promise<TleRow | null> {
  return db
    .prepare("SELECT * FROM tle_latest WHERE norad_id = ?")
    .bind(noradId)
    .first<TleRow>();
}

export async function upsertTle(
  db: D1Database,
  noradId: number,
  line1: string | null,
  line2: string | null,
  epochUtc: string | null,
  source: string,
  ommJson: string | null
): Promise<void> {
  await db
    .prepare(
      `INSERT OR REPLACE INTO tle_latest (norad_id, line1, line2, epoch_utc, source, omm_json, updated_at)
       VALUES (?, ?, ?, ?, ?, ?, datetime('now'))`
    )
    .bind(noradId, line1, line2, epochUtc, source, ommJson)
    .run();
}

export async function upsertSatellite(
  db: D1Database,
  noradId: number,
  name: string,
  intlDesignator: string | null,
  objectType: string | null
): Promise<void> {
  await db
    .prepare(
      `INSERT OR REPLACE INTO satellites (norad_id, name, intl_designator, object_type, updated_at)
       VALUES (?, ?, ?, ?, datetime('now'))`
    )
    .bind(noradId, name, intlDesignator, objectType)
    .run();
}

/** Batch upsert satellites (max 100 per batch for D1). */
export async function batchUpsertSatellites(
  db: D1Database,
  rows: Array<{ norad_id: number; name: string; intl_designator: string | null; object_type: string | null }>
): Promise<void> {
  const batchSize = 100;
  for (let i = 0; i < rows.length; i += batchSize) {
    const batch = rows.slice(i, i + batchSize);
    const stmts = batch.map((r) =>
      db
        .prepare(
          `INSERT OR REPLACE INTO satellites (norad_id, name, intl_designator, object_type, updated_at)
           VALUES (?, ?, ?, ?, datetime('now'))`
        )
        .bind(r.norad_id, r.name, r.intl_designator, r.object_type)
    );
    await db.batch(stmts);
  }
}

/** Batch upsert TLEs (max 100 per batch for D1). */
export async function batchUpsertTles(
  db: D1Database,
  rows: Array<{
    norad_id: number;
    line1: string | null;
    line2: string | null;
    epoch_utc: string | null;
    source: string;
    omm_json: string | null;
  }>
): Promise<void> {
  const batchSize = 100;
  for (let i = 0; i < rows.length; i += batchSize) {
    const batch = rows.slice(i, i + batchSize);
    const stmts = batch.map((r) =>
      db
        .prepare(
          `INSERT OR REPLACE INTO tle_latest (norad_id, line1, line2, epoch_utc, source, omm_json, updated_at)
           VALUES (?, ?, ?, ?, ?, ?, datetime('now'))`
        )
        .bind(r.norad_id, r.line1, r.line2, r.epoch_utc, r.source, r.omm_json)
    );
    await db.batch(stmts);
  }
}
