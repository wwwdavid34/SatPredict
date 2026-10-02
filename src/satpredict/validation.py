from __future__ import annotations

import csv
import gzip
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path


CANDIDATE_TIME_COLUMNS = [
    "Date_Mscan",
    "date_mscan",
    "overpass_time_utc",
    "overpass_time",
    "acquisition_time_utc",
    "acquisition_time",
    "time_utc",
    "timestamp",
    "datetime",
]


@dataclass(slots=True)
class ValidationResult:
    nearest_iso: str
    delta_seconds: float


def _parse_time(s: str) -> datetime:
    s = s.strip()
    if s.endswith("Z"):
        return datetime.fromisoformat(s.replace("Z", "+00:00")).astimezone(timezone.utc)
    try:
        dt = datetime.fromisoformat(s)
        return dt.replace(tzinfo=timezone.utc) if dt.tzinfo is None else dt.astimezone(timezone.utc)
    except ValueError:
        pass

    for fmt in ("%Y/%m/%d %H:%M:%S.%f", "%Y/%m/%d %H:%M:%S", "%Y-%m-%d %H:%M:%S.%f", "%Y-%m-%d %H:%M:%S"):
        try:
            return datetime.strptime(s, fmt).replace(tzinfo=timezone.utc)
        except ValueError:
            continue
    raise ValueError(f"Unsupported datetime format: {s}")


def nearest_event_delta(vnf_csv: str | Path, predicted_iso_utc: str) -> ValidationResult:
    predicted = _parse_time(predicted_iso_utc)
    path = Path(vnf_csv).expanduser()
    opener = gzip.open if path.suffix.lower() == ".gz" else open
    with opener(path, mode="rt", newline="", encoding="utf-8", errors="replace") as f:
        reader = csv.DictReader(f)
        cols = reader.fieldnames or []
        time_col = next((c for c in CANDIDATE_TIME_COLUMNS if c in cols), None)
        if not time_col:
            # fallback: choose first column containing 'time' or 'date'
            time_col = next((c for c in cols if "time" in c.lower() or "date" in c.lower()), None)
        if not time_col:
            raise ValueError(f"No datetime-like column found. columns={cols}")

        nearest: datetime | None = None
        best = float("inf")
        for row in reader:
            raw = (row.get(time_col) or "").strip()
            if not raw:
                continue
            try:
                dt = _parse_time(raw)
            except Exception:
                continue
            d = abs((dt - predicted).total_seconds())
            if d < best:
                best = d
                nearest = dt

        if nearest is None:
            raise ValueError("No parseable timestamps found in CSV")

    return ValidationResult(nearest_iso=nearest.isoformat().replace("+00:00", "Z"), delta_seconds=best)
