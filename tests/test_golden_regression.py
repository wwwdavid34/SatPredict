from datetime import date, datetime

from satpredict.engine import PredictionConfig, PredictionRequest, Predictor
from satpredict.models import TLE, Target


def _fixture_request(config: PredictionConfig | None = None) -> PredictionRequest:
    tle = TLE(
        name="NPP_SAMPLE",
        line1="1 37849U 11061A   15010.14957891  .00000088  00000-0  62074-4 0  9888",
        line2="2 37849  98.6834 312.3948 0001412 123.3398 352.2834 14.19582225165950",
        source="test-fixture",
    )
    return PredictionRequest(
        tle=tle,
        target=Target(lat=39.7392, lon=-104.9903, alt_m=0.0),
        start_date=date(2015, 1, 11),
        predict_days=1,
        config=config or PredictionConfig(),
    )


def test_golden_first_pass_regression_baseline():
    out = Predictor().run(_fixture_request())
    assert len(out) == 4

    first = out[sorted(out.keys(), key=int)[0]]
    assert first["exitReason"] == "converged"
    assert first["timeEndUTC"] == "2015-01-11 08:27:54"
    assert abs(first["satLat"] - 38.77879402876199) < 1e-6
    assert abs(first["satLon"] - (-96.92512544345226)) < 1e-6
    assert abs(first["distance"] - 704.4468120094344) < 1e-6
    assert abs(first["scanAngle"] - 38.95316601042776) < 1e-6


def test_offnadir_filter_excludes_wide_angles():
    cfg = PredictionConfig(max_offnadir_deg=30.0)
    out = Predictor().run(_fixture_request(cfg))
    assert len(out) == 1
    assert out["1"]["scanAngle"] < 30.0


def test_golden_runtime_knob_does_not_shift_first_pass_time():
    out_default = Predictor().run(_fixture_request(PredictionConfig(coarse_step_seconds=120)))
    out_finer = Predictor().run(_fixture_request(PredictionConfig(coarse_step_seconds=60)))

    t1 = out_default[sorted(out_default.keys(), key=int)[0]]["timeEndUTC"]
    t2 = out_finer[sorted(out_finer.keys(), key=int)[0]]["timeEndUTC"]

    dt1 = datetime.strptime(t1, "%Y-%m-%d %H:%M:%S")
    dt2 = datetime.strptime(t2, "%Y-%m-%d %H:%M:%S")
    assert abs((dt2 - dt1).total_seconds()) <= 1
