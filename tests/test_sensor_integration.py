from datetime import date

from satpredict.engine import PredictionConfig, PredictionRequest, Predictor
from satpredict.models import TLE, Target


def _fixture_req(sensor_model: str, max_offnadir: float = 30.0):
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
        config=PredictionConfig(sensor_model=sensor_model, max_offnadir_deg=max_offnadir),
    )


def test_offnadir_model_filters_more_than_pushbroom():
    p = Predictor()
    out_push = p.run(_fixture_req("pushbroom"))
    out_off = p.run(_fixture_req("offnadir", max_offnadir=30.0))

    assert len(out_off) <= len(out_push)
    if out_off:
        first = out_off[sorted(out_off.keys(), key=int)[0]]
        assert first["sensor_model"] == "offnadir"
        assert first["observable"] is True
