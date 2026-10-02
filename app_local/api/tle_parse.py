from __future__ import annotations

import json
import math
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


# ---------------------------------------------------------------------------
# OMM JSON support
# ---------------------------------------------------------------------------

# Alpha-5 upper limit — NORAD IDs beyond this cannot be encoded in TLE format.
ALPHA5_MAX = 339999


def parse_omm_record(omm: dict) -> dict:
    """Extract orbital elements from a CelesTrak OMM JSON record.

    Returns a flat dict with keys matching SGP4 element names in natural units
    (degrees, rev/day, etc.) ready for sgp4init conversion.
    """
    return {
        "norad_id": int(omm["NORAD_CAT_ID"]),
        "name": omm.get("OBJECT_NAME"),
        "epoch": omm["EPOCH"],  # ISO 8601
        "mean_motion": float(omm["MEAN_MOTION"]),  # rev/day
        "eccentricity": float(omm["ECCENTRICITY"]),
        "inclination": float(omm["INCLINATION"]),  # degrees
        "ra_of_asc_node": float(omm["RA_OF_ASC_NODE"]),  # degrees
        "arg_of_pericenter": float(omm["ARG_OF_PERICENTER"]),  # degrees
        "mean_anomaly": float(omm["MEAN_ANOMALY"]),  # degrees
        "bstar": float(omm["BSTAR"]),
        "mean_motion_dot": float(omm["MEAN_MOTION_DOT"]),  # rev/day²
        "mean_motion_ddot": float(omm["MEAN_MOTION_DDOT"]),  # rev/day³
        "classification": omm.get("CLASSIFICATION_TYPE", "U"),
        "element_set_no": int(omm.get("ELEMENT_SET_NO", 999)),
        "rev_at_epoch": int(omm.get("REV_AT_EPOCH", 0)),
        "ephemeris_type": int(omm.get("EPHEMERIS_TYPE", 0)),
        "object_id": omm.get("OBJECT_ID"),
    }


def epoch_from_omm(epoch_iso: str) -> str:
    """Convert an OMM ISO-8601 epoch string to our standard UTC format."""
    # CelesTrak uses e.g. "2024-01-15T12:34:56.789" or with trailing Z
    clean = epoch_iso.replace("Z", "+00:00")
    if "+" not in clean and clean[-1] != "Z":
        clean += "+00:00"
    dt = datetime.fromisoformat(clean)
    return dt.isoformat().replace("+00:00", "Z")


def _tle_exp_format(value: float) -> str:
    """Format a float into TLE's implicit-decimal exponential notation.

    TLE uses 5-digit mantissa + signed exponent, e.g. ' 12345-4' for 0.12345e-4.
    The leading character is a space for positive or '-' for negative values.
    Total width: 8 characters.
    """
    if value == 0.0:
        return " 00000-0"
    sign = "-" if value < 0 else " "
    av = abs(value)
    exp = math.floor(math.log10(av))
    mantissa = av / (10.0 ** exp)
    # mantissa is now in [1, 10); TLE wants it as 0.XXXXX so shift by 1
    mantissa_int = int(round(mantissa * 1e4))
    # exp was for 1.xxx form; TLE uses 0.xxxxx form so exponent += 1
    tle_exp = exp + 1
    exp_sign = "+" if tle_exp >= 0 else "-"
    return f"{sign}{mantissa_int:05d}{exp_sign}{abs(tle_exp)}"


def _tle_epoch(epoch_iso: str) -> str:
    """Convert ISO epoch to TLE epoch format: YYDDD.DDDDDDDD (14 chars)."""
    clean = epoch_iso.replace("Z", "+00:00")
    if "+" not in clean:
        clean += "+00:00"
    dt = datetime.fromisoformat(clean)
    yy = dt.year % 100
    doy = dt.timetuple().tm_yday
    frac = (dt.hour * 3600 + dt.minute * 60 + dt.second + dt.microsecond / 1e6) / 86400.0
    return f"{yy:02d}{doy + frac:012.8f}"


def _tle_checksum(line: str) -> int:
    """Compute TLE modulo-10 checksum for a 68-character line."""
    s = 0
    for ch in line[:68]:
        if ch.isdigit():
            s += int(ch)
        elif ch == "-":
            s += 1
    return s % 10


def omm_to_tle_lines(omm: dict) -> tuple[str, str] | None:
    """Synthesize standard TLE line1 + line2 from an OMM record dict.

    Returns None if the NORAD ID exceeds Alpha-5 range (>339999).
    Input is the raw OMM JSON dict (CelesTrak field names).
    """
    norad_id = int(omm["NORAD_CAT_ID"])
    if norad_id > ALPHA5_MAX:
        return None

    classification = omm.get("CLASSIFICATION_TYPE", "U")[0]
    intl_desg = (omm.get("OBJECT_ID") or "").replace("-", "").ljust(8)[:8]
    epoch_str = _tle_epoch(omm["EPOCH"])
    ndot = float(omm["MEAN_MOTION_DOT"])
    # ndot in TLE is in rev/day² ÷ 2 (half the first derivative)
    ndot_half = ndot / 2.0
    nddot = float(omm["MEAN_MOTION_DDOT"])
    # nddot in TLE is in rev/day³ ÷ 6
    nddot_sixth = nddot / 6.0
    bstar = float(omm["BSTAR"])
    eph_type = int(omm.get("EPHEMERIS_TYPE", 0))
    elset_no = int(omm.get("ELEMENT_SET_NO", 999))

    # Build line 1
    # ndot field (cols 34-43, 0-indexed 33-42): sign + '.' + 8 digits = 10 chars
    ndot_abs = abs(ndot_half)
    ndot_sign = "-" if ndot_half < 0 else " "
    # Format as 0.XXXXXXXX then strip the leading "0"
    ndot_digits = f"{ndot_abs:.8f}"[1:]  # ".00009023"
    ndot_field = f"{ndot_sign}{ndot_digits}"  # " .00009023" = 10 chars

    line1 = (
        f"1 {norad_id:05d}{classification} {intl_desg} {epoch_str}"
        f" {ndot_field} {_tle_exp_format(nddot_sixth)} {_tle_exp_format(bstar)}"
        f" {eph_type} {elset_no:4d}"
    )
    line1 = line1.ljust(68)[:68]
    line1 += str(_tle_checksum(line1))

    # Build line 2
    incl = float(omm["INCLINATION"])
    raan = float(omm["RA_OF_ASC_NODE"])
    ecc = float(omm["ECCENTRICITY"])
    argp = float(omm["ARG_OF_PERICENTER"])
    ma = float(omm["MEAN_ANOMALY"])
    mm = float(omm["MEAN_MOTION"])
    rev = int(omm.get("REV_AT_EPOCH", 0))

    ecc_str = f"{ecc:.7f}"[2:]  # drop "0."

    line2 = (
        f"2 {norad_id:05d} {incl:8.4f} {raan:8.4f} {ecc_str}"
        f" {argp:8.4f} {ma:8.4f} {mm:11.8f}{rev:5d}"
    )
    line2 = line2.ljust(68)[:68]
    line2 += str(_tle_checksum(line2))

    return line1, line2
