from datetime import date

from satpredict.engine import PredictionConfig, PredictionRequest, Predictor
from satpredict.models import TLE, Target


def test_predictor_runs_with_local_tle_and_config():
    # Historical NPP TLE sample from original project docstring/example.
    tle = TLE(
        name="NPP_SAMPLE",
        line1="1 37849U 11061A   15010.14957891  .00000088  00000-0  62074-4 0  9888",
        line2="2 37849  98.6834 312.3948 0001412 123.3398 352.2834 14.19582225165950",
        source="test-fixture",
    )

    req = PredictionRequest(
        tle=tle,
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

    out = Predictor().run(req)
    assert isinstance(out, dict)
    assert len(out) >= 1

    first = out[sorted(out.keys(), key=int)[0]]
    for k in ("timeEndUTC", "satLat", "satLon", "distance", "scanAngle", "exitReason"):
        assert k in first
    assert first["exitReason"] in {"converged", "unknown", "max_iter", "nan_state", "stalled"}
