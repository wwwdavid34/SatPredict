"""Fetch TLEs and satellite names from CelesTrak to seed the local DB."""
from __future__ import annotations

import csv
import io
import logging
import sqlite3
import urllib.request
from typing import Iterator

from app_local.api.repo import TLERecord, upsert_tle
from app_local.api.tle_parse import epoch_from_line1, norad_from_line1

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
    """Fetch TLEs from CelesTrak and insert into DB. Returns count inserted."""
    total = 0
    for group in TLE_GROUPS:
        url = CELESTRAK_TLE_URL.format(group=group)
        try:
            text = _fetch_url(url)
        except Exception as e:
            logger.warning("Failed to fetch TLE group %s: %s", group, e)
            continue

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

        conn.commit()
        total += count
        logger.info("Seeded %d TLEs from group '%s'", count, group)

    return total


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
