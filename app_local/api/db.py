from __future__ import annotations

import sqlite3
from pathlib import Path

DB_PATH = Path(__file__).resolve().parents[2] / "data" / "satpredict.db"


def connect(db_path: str | None = None) -> sqlite3.Connection:
    path = Path(db_path) if db_path else DB_PATH
    path.parent.mkdir(parents=True, exist_ok=True)
    conn = sqlite3.connect(path)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL;")
    return conn


def init_db(conn: sqlite3.Connection) -> None:
    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS tle_records (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            norad_id INTEGER NOT NULL,
            name TEXT,
            line1 TEXT,
            line2 TEXT,
            epoch_utc TEXT,
            source TEXT,
            ingested_at TEXT DEFAULT CURRENT_TIMESTAMP,
            omm_json TEXT,
            UNIQUE(norad_id, epoch_utc)
        );
        CREATE INDEX IF NOT EXISTS idx_tle_norad_epoch ON tle_records(norad_id, epoch_utc DESC);
        """
    )
    _migrate_omm_column(conn)
    conn.commit()


def _migrate_omm_column(conn: sqlite3.Connection) -> None:
    """Add omm_json column to existing databases that lack it."""
    cols = {row[1] for row in conn.execute("PRAGMA table_info(tle_records)").fetchall()}
    if "omm_json" not in cols:
        conn.execute("ALTER TABLE tle_records ADD COLUMN omm_json TEXT")
    # Relax NOT NULL on line1/line2 is handled by the new CREATE TABLE above;
    # SQLite doesn't enforce NOT NULL changes on existing rows.
