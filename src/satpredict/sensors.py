from __future__ import annotations

from dataclasses import dataclass


@dataclass(slots=True)
class SensorModel:
    """Base sensor model: decides if geometry is observable at this epoch."""

    kind: str = "generic"

    def is_observable(self, *, distance_km: float, scan_angle_deg: float, sat_alt_km: float | None = None) -> bool:
        return True


@dataclass(slots=True)
class PushBroomSensor(SensorModel):
    """Swath-limited observation with off-nadir constraint."""

    swath_km: float = 3000.0
    max_offnadir_deg: float = 55.0
    kind: str = "pushbroom"

    def is_observable(self, *, distance_km: float, scan_angle_deg: float, sat_alt_km: float | None = None) -> bool:
        return distance_km <= (self.swath_km / 2.0) and scan_angle_deg <= self.max_offnadir_deg


@dataclass(slots=True)
class OffNadirConstrainedSensor(PushBroomSensor):
    """Alias kept for backward compatibility; same behavior as PushBroomSensor."""

    kind: str = "offnadir"


def sensor_from_name(name: str, *, swath_km: float = 3000.0, max_offnadir_deg: float = 30.0) -> SensorModel:
    n = (name or "pushbroom").strip().lower()
    if n in {"pushbroom", "legacy", "default"}:
        return PushBroomSensor(swath_km=swath_km, max_offnadir_deg=max_offnadir_deg)
    if n in {"offnadir", "off-nadir", "target-centric"}:
        return OffNadirConstrainedSensor(swath_km=swath_km, max_offnadir_deg=max_offnadir_deg)
    raise ValueError(f"Unknown sensor model: {name}")
