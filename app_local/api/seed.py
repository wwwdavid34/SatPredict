"""Fetch TLEs and satellite names from CelesTrak to seed the local DB."""
from __future__ import annotations

import csv
import io
import json
import logging
import sqlite3
import urllib.request
from typing import Iterator

from app_local.api.repo import TLERecord, upsert_tle
from app_local.api.tle_parse import (
    ALPHA5_MAX,
    epoch_from_line1,
    epoch_from_omm,
    norad_from_line1,
    omm_to_tle_lines,
    parse_omm_record,
)

logger = logging.getLogger(__name__)

# CelesTrak TLE groups to fetch (covers most useful satellites)
TLE_GROUPS = [
    "stations",       # ISS, Tiangong, etc.
    "active",         # All active satellites (large, ~7k)
    "weather",        # Weather sats
    "noaa",           # NOAA fleet
    "resource",       # Earth resources (Landsat, etc.)
    "sarsat",         # Search & rescue
    "science",        # Science missions
]

CELESTRAK_TLE_URL = "https://celestrak.org/NORAD/elements/gp.php?GROUP={group}&FORMAT=tle"
CELESTRAK_OMM_URL = "https://celestrak.org/NORAD/elements/gp.php?GROUP={group}&FORMAT=json"
CELESTRAK_SATCAT_URL = "https://celestrak.org/pub/satcat.csv"
USER_AGENT = "SatPredict/0.1"


def _fetch_url(url: str) -> str:
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(req, timeout=60) as resp:
        return resp.read().decode("utf-8")


def _iter_tles_from_text(text: str) -> Iterator[tuple[str | None, str, str]]:
    """Parse 3-line or 2-line TLE format from text."""
    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    i = 0
    while i < len(lines):
        cur = lines[i]
        # 3-line format: name + line1 + line2
        if (
            i + 2 < len(lines)
            and not cur.startswith("1 ")
            and lines[i + 1].startswith("1 ")
            and lines[i + 2].startswith("2 ")
        ):
            yield cur, lines[i + 1], lines[i + 2]
            i += 3
            continue
        # 2-line format: line1 + line2
        if i + 1 < len(lines) and cur.startswith("1 ") and lines[i + 1].startswith("2 "):
            yield None, cur, lines[i + 1]
            i += 2
            continue
        i += 1


def seed_tles(conn: sqlite3.Connection) -> int:
    """Fetch OMM JSON from CelesTrak and insert into DB.

    For NORAD IDs within Alpha-5 range (≤339999), TLE lines are synthesized
    from OMM fields for backward compatibility.  For IDs beyond that range,
    only omm_json is stored and propagation uses sgp4init() directly.

    Falls back to legacy TLE text fetch if the JSON request fails.
    Returns total count inserted.
    """
    total = 0
    for group in TLE_GROUPS:
        # Try OMM JSON first, fall back to TLE text
        url = CELESTRAK_OMM_URL.format(group=group)
        try:
            text = _fetch_url(url)
            records = json.loads(text)
            count = _seed_from_omm(conn, records, group)
        except Exception as e:
            logger.warning("OMM fetch failed for group %s (%s), falling back to TLE", group, e)
            count = _seed_from_tle_text(conn, group)

        conn.commit()
        total += count
        logger.info("Seeded %d records from group '%s'", count, group)

    return total


def _seed_from_omm(conn: sqlite3.Connection, records: list[dict], group: str) -> int:
    """Ingest a list of CelesTrak OMM JSON records."""
    count = 0
    for omm in records:
        try:
            parsed = parse_omm_record(omm)
        except (KeyError, ValueError) as e:
            logger.debug("Skipping malformed OMM record: %s", e)
            continue

        norad_id = parsed["norad_id"]
        epoch_utc = epoch_from_omm(parsed["epoch"])

        # Synthesize TLE lines when possible
        tle_pair = omm_to_tle_lines(omm)
        line1 = tle_pair[0] if tle_pair else None
        line2 = tle_pair[1] if tle_pair else None

        # Store omm_json for all records (useful for OMM-only propagation)
        omm_blob = json.dumps(omm, separators=(",", ":"))

        rec = TLERecord(
            norad_id=norad_id,
            name=parsed["name"],
            line1=line1,
            line2=line2,
            epoch_utc=epoch_utc,
            source=f"celestrak:{group}",
            omm_json=omm_blob,
        )
        upsert_tle(conn, rec)
        count += 1
    return count


def _seed_from_tle_text(conn: sqlite3.Connection, group: str) -> int:
    """Legacy fallback: fetch and parse TLE text format."""
    url = CELESTRAK_TLE_URL.format(group=group)
    try:
        text = _fetch_url(url)
    except Exception as e:
        logger.warning("Failed to fetch TLE group %s: %s", group, e)
        return 0

    count = 0
    for name, l1, l2 in _iter_tles_from_text(text):
        try:
            norad = norad_from_line1(l1)
        except Exception:
            continue
        rec = TLERecord(
            norad_id=norad,
            name=name,
            line1=l1,
            line2=l2,
            epoch_utc=epoch_from_line1(l1),
            source=f"celestrak:{group}",
        )
        upsert_tle(conn, rec)
        count += 1
    return count


def seed_names(conn: sqlite3.Connection) -> int:
    """Fetch satellite catalog from CelesTrak and update names. Returns count updated."""
    try:
        text = _fetch_url(CELESTRAK_SATCAT_URL)
    except Exception as e:
        logger.warning("Failed to fetch satellite catalog: %s", e)
        return 0

    reader = csv.DictReader(io.StringIO(text))
    names: dict[int, str] = {}
    for row in reader:
        try:
            norad = int(row["NORAD_CAT_ID"])
            name = row.get("OBJECT_NAME", "").strip()
            if name:
                names[norad] = name
        except (ValueError, KeyError):
            continue

    rows = conn.execute(
        "SELECT DISTINCT norad_id FROM tle_records WHERE name IS NULL OR name = ''"
    ).fetchall()

    updated = 0
    for r in rows:
        norad = r[0]
        if norad in names:
            conn.execute(
                "UPDATE tle_records SET name = ? WHERE norad_id = ?",
                (names[norad], norad),
            )
            updated += 1

    conn.commit()
    logger.info("Updated %d satellite names from catalog", updated)
    return updated


def seed_if_empty(conn: sqlite3.Connection) -> None:
    """Seed DB only if it has no TLE records."""
    count = conn.execute("SELECT COUNT(*) FROM tle_records").fetchone()[0]
    if count > 0:
        logger.info("DB already has %d TLE records, skipping seed.", count)
        return
    logger.info("DB is empty, seeding from CelesTrak...")
    n_tles = seed_tles(conn)
    n_names = seed_names(conn)
    logger.info("Seed complete: %d TLEs, %d names updated.", n_tles, n_names)


def refresh(conn: sqlite3.Connection) -> None:
    """Full refresh: fetch latest TLEs and update names."""
    logger.info("Refreshing TLE data from CelesTrak...")
    n_tles = seed_tles(conn)
    n_names = seed_names(conn)
    logger.info("Refresh complete: %d TLEs, %d names updated.", n_tles, n_names)
