"""Verify the /api/predict/overpass response includes TLE and swath_km."""
import pytest

pytest.importorskip("fastapi")
from fastapi.testclient import TestClient
from app_local.api.main import app


@pytest.fixture
def client():
    return TestClient(app)


def test_overpass_response_includes_tle_and_swath(client):
    """Response must include tle.line1, tle.line2, and swath_km."""
    r = client.get(
        "/api/predict/overpass",
        params={
            "norad_id": 25544,
            "target_lat": 39.7392,
            "target_lon": -104.9903,
            "predict_days": 1,
            "sensor_model": "pushbroom",
        },
    )
    if r.status_code == 404:
        pytest.skip("No TLE data for 25544 in test DB")
    assert r.status_code == 200
    body = r.json()
    assert "tle" in body
    assert "line1" in body["tle"]
    assert "line2" in body["tle"]
    assert "swath_km" in body
    assert isinstance(body["swath_km"], (int, float))
