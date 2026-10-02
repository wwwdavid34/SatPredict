from datetime import date

from satpredict.engine import PredictionConfig, PredictionRequest, PredictionResult, Predictor
from satpredict.models import TLE, Target

# Historical NPP TLE sample (polar orbit, inclination ~98.7°).
NPP_TLE = TLE(
    name="NPP_SAMPLE",
    line1="1 37849U 11061A   15010.14957891  .00000088  00000-0  62074-4 0  9888",
    line2="2 37849  98.6834 312.3948 0001412 123.3398 352.2834 14.19582225165950",
    source="test-fixture",
)

# ISS TLE sample (low inclination ~51.6°).
ISS_TLE = TLE(
    name="ISS",
    line1="1 25544U 98067A   24045.54896378  .00016717  00000-0  10270-3 0  9025",
    line2="2 25544  51.6400 208.9163 0002839 128.1013 231.9987 15.49989633 20000",
    source="test-fixture",
)


def test_predictor_runs_with_local_tle_and_config():
    req = PredictionRequest(
        tle=NPP_TLE,
        target=Target(lat=39.7392, lon=-104.9903, alt_m=0.0),
        start_date=date(2015, 1, 11),
        predict_days=1,
        config=PredictionConfig(
            coarse_step_seconds=120.0,
            iteration_limit=1000,
            swath_km=3000.0,
            bearing_precision_deg=0.0001,
        ),
    )

    result = Predictor().run(req)
    assert isinstance(result, PredictionResult)
    assert result.reachable is True
    assert len(result.passes) >= 1

    first = result.passes[sorted(result.passes.keys(), key=int)[0]]
    for k in ("timeEndUTC", "satLat", "satLon", "distance", "scanAngle", "exitReason"):
        assert k in first
    assert first["exitReason"] in {"converged", "unknown", "max_iter", "nan_state", "stalled"}


def test_unreachable_iss_high_latitude():
    """ISS (inclination ~51.6°) targeting Tromsø (69.6°N) should be flagged
    as unreachable even at the default 55° off-nadir.  At ~420 km altitude,
    55° off-nadir gives ~5.8° earth-central-angle margin → max ≈ 57.4°."""
    p = Predictor()
    satrec = p._legacy_satrec(ISS_TLE.line1, ISS_TLE.line2)

    result = Predictor.check_reachability(satrec, target_lat=69.6, max_offnadir_deg=55.0)
    assert isinstance(result, PredictionResult)
    assert result.reachable is False
    assert result.passes == {}
    assert result.inclination_deg is not None
    assert result.inclination_deg < 52.0
    assert result.max_latitude_deg is not None
    assert result.max_latitude_deg < 60.0
    assert "never" in result.reason.lower()


def test_reachable_iss_mid_latitude():
    """ISS targeting Denver (39.7°N) should pass the reachability check."""
    p = Predictor()
    satrec = p._legacy_satrec(ISS_TLE.line1, ISS_TLE.line2)
    result = Predictor.check_reachability(satrec, target_lat=39.7392, max_offnadir_deg=55.0)
    assert result is None  # None means reachable
