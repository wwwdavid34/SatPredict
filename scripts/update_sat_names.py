#!/usr/bin/env python3
"""Fetch satellite catalog from CelesTrak and update names in the local DB."""
from __future__ import annotations

import csv
import io
import urllib.request

from app_local.api.db import connect

SATCAT_URL = "https://celestrak.org/pub/satcat.csv"


def main():
    print("Fetching satellite catalog from CelesTrak...")
    req = urllib.request.Request(SATCAT_URL, headers={"User-Agent": "SatPredict/0.1"})
    with urllib.request.urlopen(req, timeout=30) as resp:
        text = resp.read().decode("utf-8")

    reader = csv.DictReader(io.StringIO(text))
    # Build NORAD -> name mapping
    names: dict[int, str] = {}
    for row in reader:
        try:
            norad = int(row["NORAD_CAT_ID"])
            name = row.get("OBJECT_NAME", "").strip()
            if name:
                names[norad] = name
        except (ValueError, KeyError):
            continue

    print(f"Loaded {len(names)} satellite names from catalog.")

    conn = connect()
    # Get distinct NORAD IDs that have no name
    rows = conn.execute(
        "SELECT DISTINCT norad_id FROM tle_records WHERE name IS NULL OR name = ''"
    ).fetchall()
    missing = [r[0] for r in rows]
    print(f"Found {len(missing)} NORAD IDs with no name in DB.")

    updated = 0
    for norad in missing:
        if norad in names:
            conn.execute(
                "UPDATE tle_records SET name = ? WHERE norad_id = ?",
                (names[norad], norad),
            )
            updated += 1

    conn.commit()
    conn.close()
    print(f"Updated {updated} satellites with names.")


if __name__ == "__main__":
    main()
