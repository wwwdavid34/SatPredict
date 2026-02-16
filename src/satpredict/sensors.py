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
    """Current legacy behavior equivalent: swath-limited observation."""

    swath_km: float = 3000.0
    kind: str = "pushbroom"

    def is_observable(self, *, distance_km: float, scan_angle_deg: float, sat_alt_km: float | None = None) -> bool:
        return distance_km <= (self.swath_km / 2.0)


@dataclass(slots=True)
class OffNadirConstrainedSensor(PushBroomSensor):
    """Adds off-nadir (scan angle) constraint on top of swath footprint."""

    max_offnadir_deg: float = 30.0
    kind: str = "offnadir"

    def is_observable(self, *, distance_km: float, scan_angle_deg: float, sat_alt_km: float | None = None) -> bool:
        return PushBroomSensor.is_observable(self, distance_km=distance_km, scan_angle_deg=scan_angle_deg, sat_alt_km=sat_alt_km) and (
            scan_angle_deg <= self.max_offnadir_deg
        )


def sensor_from_name(name: str, *, swath_km: float = 3000.0, max_offnadir_deg: float = 30.0) -> SensorModel:
    n = (name or "pushbroom").strip().lower()
    if n in {"pushbroom", "legacy", "default"}:
        return PushBroomSensor(swath_km=swath_km)
    if n in {"offnadir", "off-nadir", "target-centric"}:
        return OffNadirConstrainedSensor(swath_km=swath_km, max_offnadir_deg=max_offnadir_deg)
    raise ValueError(f"Unknown sensor model: {name}")
