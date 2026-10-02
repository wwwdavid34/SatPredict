from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime


@dataclass(slots=True)
class TLE:
    name: str | None
    line1: str | None
    line2: str | None
    source: str
    omm_data: dict | None = None


@dataclass(slots=True)
class Target:
    lat: float
    lon: float
    alt_m: float = 0.0


@dataclass(slots=True)
class PassWindow:
    aos_utc: datetime
    los_utc: datetime
    peak_elevation_deg: float | None = None
