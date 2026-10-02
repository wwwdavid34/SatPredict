from __future__ import annotations

import math
from dataclasses import dataclass, field
from datetime import date
from pathlib import Path
import importlib.util
import sys

from .models import TLE, Target
from .sensors import PushBroomSensor

EARTH_RADIUS_KM = 6378.137
DEG2RAD = math.pi / 180.0
KM_PER_DEG_LAT = 111.0  # approximate km per degree of latitude


def solar_elevation(utc_str: str, lat: float, lon: float) -> float:
    """Approximate solar elevation angle (degrees) at a surface location.

    Uses the simple "solar declination + hour angle" model, accurate to ~1°.
    Returns negative values when the sun is below the horizon.
    """
    from datetime import datetime

    dt = datetime.strptime(utc_str, "%Y-%m-%d %H:%M:%S")
    # Day of year and fractional hour (UTC)
    doy = dt.timetuple().tm_yday
    hour_utc = dt.hour + dt.minute / 60.0 + dt.second / 3600.0

    # Solar declination (Spencer, 1971)
    gamma = 2.0 * math.pi * (doy - 1) / 365.0
    decl = (0.006918 - 0.399912 * math.cos(gamma) + 0.070257 * math.sin(gamma)
            - 0.006758 * math.cos(2 * gamma) + 0.000907 * math.sin(2 * gamma)
            - 0.002697 * math.cos(3 * gamma) + 0.00148 * math.sin(3 * gamma))

    # Equation of time (minutes)
    eqtime = 229.18 * (0.000075 + 0.001868 * math.cos(gamma)
             - 0.032077 * math.sin(gamma)
             - 0.014615 * math.cos(2 * gamma)
             - 0.04089 * math.sin(2 * gamma))

    # Solar hour angle
    solar_time = hour_utc * 60.0 + eqtime + 4.0 * lon  # minutes
    ha = DEG2RAD * (solar_time / 4.0 - 180.0)

    lat_r = DEG2RAD * lat
    elev = math.asin(
        math.sin(lat_r) * math.sin(decl)
        + math.cos(lat_r) * math.cos(decl) * math.cos(ha)
    )
    return math.degrees(elev)


def offnadir_to_ground_km(offnadir_deg: float, sat_alt_km: float) -> float:
    """Ground-arc distance (km) corresponding to an off-nadir angle at a given altitude.

    Uses the satellite–Earth-center triangle (C=center, S=satellite, G=ground):
        sin(gamma) / (R + h) = sin(theta) / R
    At nadir (theta=0) the angle at G is 180° (C-G-S collinear), so the
    correct branch is gamma = pi - arcsin(...), giving:
        alpha = arcsin((R+h)/R * sin(theta)) - theta
    """
    theta = math.radians(offnadir_deg)
    R = EARTH_RADIUS_KM
    sin_val = (R + sat_alt_km) / R * math.sin(theta)
    if sin_val >= 1.0:
        # Off-nadir exceeds horizon — sensor sees to the tangent point.
        return R * math.acos(R / (R + sat_alt_km))
    alpha = math.asin(sin_val) - theta
    return R * alpha


@dataclass(slots=True)
class PredictionConfig:
    coarse_step_seconds: float = 120.0
    iteration_limit: int = 1000
    swath_km: float = 3000.0
    bearing_precision_deg: float = 0.0001
    min_step_seconds: float = 0.005
    max_stall_iterations: int = 30
    max_offnadir_deg: float = 55.0


@dataclass(slots=True)
class PredictionRequest:
    tle: TLE
    target: Target
    start_date: date
    predict_days: int = 1
    config: PredictionConfig = field(default_factory=PredictionConfig)


@dataclass(slots=True)
class PredictionResult:
    passes: dict[str, dict]
    reachable: bool = True
    max_latitude_deg: float | None = None
    inclination_deg: float | None = None
    offnadir_margin_deg: float | None = None
    apogee_alt_km: float | None = None
    reason: str | None = None


class Predictor:
    """Thin wrapper over legacy SatPredict class while refactor is in progress."""

    _tf = None  # shared TimezoneFinder instance (lazy-loaded)

    def __init__(self, repo_root: str | Path | None = None) -> None:
        self.repo_root = Path(repo_root or Path(__file__).resolve().parents[2])
        self._legacy_cls = self._load_legacy_class()

    def _load_legacy_class(self):
        path = self.repo_root / "SatPredict.py"
        if str(self.repo_root) not in sys.path:
            sys.path.insert(0, str(self.repo_root))
        spec = importlib.util.spec_from_file_location("satpredict_legacy", path)
        if not spec or not spec.loader:
            raise RuntimeError(f"Failed to load legacy module from {path}")
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        self._legacy_mod = mod
        return mod.SatPredict

    @classmethod
    def _utc_offset_hours(cls, lat: float, lon: float, d: date) -> float:
        """Return the UTC offset in hours for a location and date,
        using political timezone boundaries (handles DST)."""
        from zoneinfo import ZoneInfo
        from datetime import datetime
        from timezonefinder import TimezoneFinder

        if cls._tf is None:
            cls._tf = TimezoneFinder()
        tz_name = cls._tf.timezone_at(lat=lat, lng=lon)
        if tz_name is None:
            return round(lon / 15.0)  # ocean fallback
        tz = ZoneInfo(tz_name)
        offset = datetime(d.year, d.month, d.day, 12, tzinfo=tz).utcoffset()
        return offset.total_seconds() / 3600.0

    @staticmethod
    def check_reachability(
        satrec, target_lat: float, max_offnadir_deg: float,
    ) -> PredictionResult | None:
        """Return a failed PredictionResult if the target is geometrically
        unreachable given the satellite's orbital inclination, or None if
        the target is potentially reachable.

        Coverage margin is derived from the max off-nadir angle at apogee
        altitude (most generous bound).  Swath width is just the ground
        projection of this same angle, so only one is needed.
        """
        inclination_deg = math.degrees(satrec.inclo)
        apogee_alt_km = satrec.alta * EARTH_RADIUS_KM
        margin_km = offnadir_to_ground_km(max_offnadir_deg, apogee_alt_km)
        margin_deg = margin_km / KM_PER_DEG_LAT
        max_latitude_deg = inclination_deg + margin_deg

        if abs(target_lat) > max_latitude_deg:
            return PredictionResult(
                passes={},
                reachable=False,
                max_latitude_deg=round(max_latitude_deg, 2),
                inclination_deg=round(inclination_deg, 2),
                offnadir_margin_deg=round(margin_deg, 2),
                apogee_alt_km=round(apogee_alt_km, 1),
                reason=(
                    f"Target latitude {target_lat:.1f}\u00b0 is beyond the satellite's "
                    f"maximum coverage latitude of \u00b1{max_latitude_deg:.1f}\u00b0. "
                    f"This satellite can never observe this target."
                ),
            )
        return None

    def run(self, request: PredictionRequest) -> PredictionResult:
        cfg = request.config
        # Expose precision/runtime knobs without changing legacy defaults.
        self._legacy_mod.tspanDef = float(cfg.coarse_step_seconds)
        self._legacy_mod.iteLimitDef = int(cfg.iteration_limit)
        self._legacy_mod.swath = float(cfg.swath_km)

        p = self._legacy_cls()
        p.bearingPrecision = float(cfg.bearing_precision_deg)
        p.minStepSeconds = float(cfg.min_step_seconds)
        p.maxStallIterations = int(cfg.max_stall_iterations)
        # Bypass legacy online TLE fetch path; inject satrec directly.
        p.tleL1 = request.tle.line1
        p.tleL2 = request.tle.line2
        p.tleL1Input = None
        p.tleL2Input = None

        # Choose satrec construction path: TLE lines (legacy) or OMM direct
        if request.tle.line1 and request.tle.line2:
            p.satrec = self._legacy_satrec(request.tle.line1, request.tle.line2)
        elif request.tle.omm_data:
            p.satrec = self._omm_satrec(request.tle.omm_data)
        else:
            raise ValueError("TLE record has neither TLE lines nor OMM data")
        p.get_satrec = lambda *args, **kwargs: p.satrec

        # --- Reachability guard ---
        # Skip propagation entirely if the orbit can never reach the target.
        unreachable = self.check_reachability(
            p.satrec, request.target.lat, cfg.max_offnadir_deg,
        )
        if unreachable is not None:
            return unreachable

        p.startDate = request.start_date.isoformat()
        p.predictDays = int(request.predict_days)
        p.verbose = False
        p.obsPos["lat"] = request.target.lat
        p.obsPos["lon"] = request.target.lon
        p.obsPos["alt"] = request.target.alt_m
        p.timeZone = self._utc_offset_hours(
            request.target.lat, request.target.lon, request.start_date,
        )

        # Use internal compute entrypoint directly to avoid legacy network-coupled checks.
        from datetime import datetime

        start_dt = datetime.fromisoformat(request.start_date.isoformat())
        start_jt = p.date2jd(start_dt)
        raw = p._run_predict(p.satrec, start_jt, p.obsPos, p.predictDays, p.verbose)

        inclination_deg = math.degrees(p.satrec.inclo)
        apogee_alt_km = p.satrec.alta * EARTH_RADIUS_KM
        margin_km = offnadir_to_ground_km(cfg.max_offnadir_deg, apogee_alt_km)
        max_latitude_deg = inclination_deg + margin_km / KM_PER_DEG_LAT

        sensor = PushBroomSensor(swath_km=cfg.swath_km, max_offnadir_deg=cfg.max_offnadir_deg)
        filtered: dict[str, dict] = {}
        idx = 0
        for key in sorted(raw.keys(), key=int):
            row = raw[key]
            observable = sensor.is_observable(
                distance_km=float(row.get("distance", 1e18)),
                scan_angle_deg=float(row.get("scanAngle", 1e18)),
                sat_alt_km=float(row.get("satAlt", 0.0)) if row.get("satAlt") is not None else None,
            )
            if observable:
                idx += 1
                row = dict(row)
                row["sensor_model"] = sensor.kind
                row["observable"] = True
                # Separate orbit direction from solar illumination.
                row["ascending"] = row.get("dayNight", 0)  # legacy: velZ>0
                utc_str = row.get("timeEndUTC", "")
                if utc_str:
                    sun_elev = solar_elevation(utc_str, request.target.lat, request.target.lon)
                    row["dayNight"] = 1 if sun_elev > 0 else 0
                    row["solarElevation"] = round(sun_elev, 1)
                filtered[str(idx)] = row
        return PredictionResult(
            passes=filtered,
            reachable=True,
            max_latitude_deg=round(max_latitude_deg, 2),
            inclination_deg=round(inclination_deg, 2),
            offnadir_margin_deg=round(margin_km / KM_PER_DEG_LAT, 2),
            apogee_alt_km=round(apogee_alt_km, 1),
        )

    def _legacy_satrec(self, line1: str, line2: str):
        from sgp4 import io
        from sgp4.earth_gravity import wgs72

        return io.twoline2rv(line1, line2, wgs72)

    @staticmethod
    def _omm_satrec(omm: dict):
        """Construct satrec directly from parsed OMM elements via sgp4init().

        This path is used when TLE lines cannot represent the satellite
        (e.g. NORAD ID > 339999 exceeding Alpha-5 encoding).

        ``omm`` is the dict returned by ``parse_omm_record()``, with orbital
        elements in natural units (degrees, rev/day).
        """
        from sgp4.propagation import sgp4init
        from sgp4.earth_gravity import wgs72
        from sgp4.model import Satellite
        from sgp4.ext import jday

        satrec = Satellite()
        satrec.error = 0
        satrec.whichconst = wgs72

        deg2rad = math.pi / 180.0
        xpdotp = 1440.0 / (2.0 * math.pi)  # rev/day → rad/min factor

        # Mean motion: rev/day → rad/min (SGP4 internal unit)
        xno = omm["mean_motion"] / xpdotp

        # Parse epoch ISO string to Julian date
        epoch_str = omm["epoch"].replace("Z", "+00:00")
        if "+" not in epoch_str and not epoch_str.endswith("+00:00"):
            epoch_str += "+00:00"
        from datetime import datetime as _dt
        epoch_dt = _dt.fromisoformat(epoch_str)
        epoch_jd = jday(
            epoch_dt.year, epoch_dt.month, epoch_dt.day,
            epoch_dt.hour, epoch_dt.minute,
            epoch_dt.second + epoch_dt.microsecond / 1e6,
        )

        # Set attributes that sgp4init and downstream code expect
        satrec.satnum = omm["norad_id"]
        satrec.epochyr = epoch_dt.year
        satrec.epochdays = (
            epoch_dt.timetuple().tm_yday
            + (epoch_dt.hour * 3600 + epoch_dt.minute * 60
               + epoch_dt.second + epoch_dt.microsecond / 1e6) / 86400.0
        )
        satrec.jdsatepoch = epoch_jd
        satrec.epoch = epoch_dt.replace(tzinfo=None)

        # ndot/nddot stored but ignored by SGP4; set for completeness
        satrec.ndot = omm["mean_motion_dot"] / (xpdotp * 1440.0)
        satrec.nddot = omm["mean_motion_ddot"] / (xpdotp * 1440.0 * 1440.0)

        sgp4init(
            wgs72, "i", omm["norad_id"],
            epoch_jd - 2433281.5,  # epoch in days since 1949-12-31 00:00 UT
            omm["bstar"],
            omm["eccentricity"],
            omm["arg_of_pericenter"] * deg2rad,
            omm["inclination"] * deg2rad,
            omm["mean_anomaly"] * deg2rad,
            xno,
            omm["ra_of_asc_node"] * deg2rad,
            satrec,
        )
        return satrec
