from datetime import date

from satpredict.engine import PredictionConfig, PredictionRequest, Predictor
from satpredict.models import TLE, Target


def _fixture_req(max_offnadir: float = 55.0):
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
        config=PredictionConfig(max_offnadir_deg=max_offnadir),
    )


def test_tighter_offnadir_filters_more():
    p = Predictor()
    out_wide = p.run(_fixture_req(max_offnadir=55.0))
    out_tight = p.run(_fixture_req(max_offnadir=30.0))

    assert len(out_tight) < len(out_wide)
    for key in out_tight:
        assert out_tight[key]["scanAngle"] <= 30.0
        assert out_tight[key]["observable"] is True
