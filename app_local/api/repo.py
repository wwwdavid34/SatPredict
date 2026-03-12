from __future__ import annotations

from dataclasses import dataclass
import sqlite3


@dataclass(slots=True)
class TLERecord:
    norad_id: int
    name: str | None
    line1: str | None
    line2: str | None
    epoch_utc: str | None
    source: str | None
    omm_json: str | None = None


def list_satellites(conn: sqlite3.Connection, q: str = "", limit: int = 50):
    like = f"%{q}%"
    rows = conn.execute(
        """
        SELECT norad_id, MAX(epoch_utc) AS latest_epoch, MAX(name) AS name, COUNT(*) AS tle_count
        FROM tle_records
        WHERE (? = '' OR CAST(norad_id AS TEXT) LIKE ? OR COALESCE(name,'') LIKE ?)
        GROUP BY norad_id
        ORDER BY latest_epoch DESC
        LIMIT ?
        """,
        (q, like, like, limit),
    ).fetchall()
    return [dict(r) for r in rows]


def get_latest_tle(conn: sqlite3.Connection, norad_id: int) -> TLERecord | None:
    row = conn.execute(
        """
        SELECT norad_id, name, line1, line2, epoch_utc, source, omm_json
        FROM tle_records
        WHERE norad_id = ?
        ORDER BY epoch_utc DESC
        LIMIT 1
        """,
        (norad_id,),
    ).fetchone()
    if not row:
        return None
    return TLERecord(**dict(row))


def upsert_tle(conn: sqlite3.Connection, rec: TLERecord) -> None:
    conn.execute(
        """
        INSERT OR IGNORE INTO tle_records(norad_id, name, line1, line2, epoch_utc, source, omm_json)
        VALUES(?,?,?,?,?,?,?)
        """,
        (rec.norad_id, rec.name, rec.line1, rec.line2, rec.epoch_utc, rec.source, rec.omm_json),
    )
