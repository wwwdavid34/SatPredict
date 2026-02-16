from __future__ import annotations

from datetime import datetime, timedelta, timezone


def norad_from_line1(line1: str) -> int:
    # line1 cols 3-7 in standard TLE (1-based)
    return int(line1[2:7].strip())


def epoch_from_line1(line1: str) -> str | None:
    # cols 19-32: YYDDD.DDDDDDDD
    raw = line1[18:32].strip()
    if not raw:
        return None
    yy = int(raw[:2])
    doy = float(raw[2:])
    year = 1900 + yy if yy >= 57 else 2000 + yy
    start = datetime(year, 1, 1, tzinfo=timezone.utc)
    dt = start + timedelta(days=doy - 1)
    return dt.isoformat().replace('+00:00', 'Z')
