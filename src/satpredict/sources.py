from __future__ import annotations

from pathlib import Path
from urllib.request import urlopen
from zipfile import ZipFile
from io import TextIOWrapper

from .models import TLE


def fetch_celestrak_group(group: str = "starlink") -> list[TLE]:
    url = f"https://celestrak.org/NORAD/elements/gp.php?GROUP={group}&FORMAT=tle"
    raw = urlopen(url, timeout=30).read().decode("utf-8", errors="replace")
    lines = [ln.strip() for ln in raw.splitlines() if ln.strip()]
    out: list[TLE] = []
    i = 0
    while i + 2 < len(lines):
        name, l1, l2 = lines[i], lines[i + 1], lines[i + 2]
        if l1.startswith("1 ") and l2.startswith("2 "):
            out.append(TLE(name=name, line1=l1, line2=l2, source=url))
            i += 3
        else:
            i += 1
    return out


def load_tles_from_zip(zip_path: str | Path, limit: int | None = None) -> list[TLE]:
    zip_path = Path(zip_path).expanduser()
    out: list[TLE] = []
    with ZipFile(zip_path) as zf:
        members = [m for m in zf.namelist() if m.lower().endswith((".txt", ".tle"))]
        for member in members:
            with zf.open(member) as fh:
                text = TextIOWrapper(fh, encoding="utf-8", errors="replace").read().splitlines()
            lines = [ln.strip() for ln in text if ln.strip()]
            i = 0
            while i + 2 < len(lines):
                name, l1, l2 = lines[i], lines[i + 1], lines[i + 2]
                if l1.startswith("1 ") and l2.startswith("2 "):
                    out.append(TLE(name=name, line1=l1, line2=l2, source=f"zip:{zip_path.name}:{member}"))
                    if limit and len(out) >= limit:
                        return out
                    i += 3
                else:
                    i += 1
    return out
