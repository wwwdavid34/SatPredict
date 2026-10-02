#!/usr/bin/env python3
from __future__ import annotations

import argparse
from io import TextIOWrapper
from zipfile import ZipFile

from app_local.api.db import connect, init_db
from app_local.api.repo import TLERecord, upsert_tle
from app_local.api.tle_parse import epoch_from_line1, norad_from_line1


def iter_tles_from_text(text: str):
    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    i = 0
    while i < len(lines):
        cur = lines[i]
        # 3-line TLE format (name + line1 + line2)
        if i + 2 < len(lines) and (not cur.startswith('1 ')) and lines[i + 1].startswith('1 ') and lines[i + 2].startswith('2 '):
            yield cur, lines[i + 1], lines[i + 2]
            i += 3
            continue
        # 2-line TLE format (line1 + line2)
        if i + 1 < len(lines) and cur.startswith('1 ') and lines[i + 1].startswith('2 '):
            yield None, cur, lines[i + 1]
            i += 2
            continue
        i += 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--outer-zip', default='/home/david/Downloads/TLEs.zip')
    ap.add_argument('--max-records', type=int, default=300000)
    ap.add_argument('--year-filter', default='2025', help='e.g. 2025 or empty for all')
    args = ap.parse_args()

    conn = connect()
    init_db(conn)

    inserted = 0
    with ZipFile(args.outer_zip) as outer:
        inner_names = [n for n in outer.namelist() if n.lower().endswith('.zip')]
        if args.year_filter:
            inner_names = [n for n in inner_names if args.year_filter in n]

        for iname in sorted(inner_names):
            with outer.open(iname) as fh:
                # inner zip bytes stream
                data = fh.read()
            from io import BytesIO
            with ZipFile(BytesIO(data)) as inner:
                for member in inner.namelist():
                    if not member.lower().endswith(('.txt', '.tle')):
                        continue
                    with inner.open(member) as tf:
                        text = TextIOWrapper(tf, encoding='utf-8', errors='replace').read()
                    for name, l1, l2 in iter_tles_from_text(text):
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
                            source=f'zip:{iname}:{member}',
                        )
                        upsert_tle(conn, rec)
                        inserted += 1
                        if inserted % 10000 == 0:
                            conn.commit()
                            print(f'processed={inserted}')
                        if inserted >= args.max_records:
                            conn.commit()
                            print(f'done max_records={inserted}')
                            return
    conn.commit()
    print(f'done processed={inserted}')


if __name__ == '__main__':
    main()
