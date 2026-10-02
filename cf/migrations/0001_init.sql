-- Satellite catalog: stable metadata for fast search
CREATE TABLE IF NOT EXISTS satellites (
    norad_id INTEGER PRIMARY KEY,
    name TEXT NOT NULL,
    intl_designator TEXT,
    object_type TEXT,
    updated_at TEXT DEFAULT CURRENT_TIMESTAMP
);
CREATE INDEX IF NOT EXISTS idx_sat_name ON satellites(name);

-- Latest TLE/OMM per satellite (one row each, replaced on refresh)
CREATE TABLE IF NOT EXISTS tle_latest (
    norad_id INTEGER PRIMARY KEY,
    line1 TEXT,
    line2 TEXT,
    epoch_utc TEXT,
    source TEXT,
    omm_json TEXT,
    updated_at TEXT DEFAULT CURRENT_TIMESTAMP
);
