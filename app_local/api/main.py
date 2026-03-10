from __future__ import annotations

import asyncio
import logging
from contextlib import asynccontextmanager
from datetime import date, datetime, timedelta

from fastapi import FastAPI, HTTPException, Query
from fastapi.middleware.cors import CORSMiddleware

from app_local.api.db import connect, init_db
from app_local.api.repo import get_latest_tle, list_satellites
from app_local.api.seed import refresh, seed_if_empty
from satpredict.engine import PredictionConfig, PredictionRequest, Predictor
from satpredict.models import TLE, Target

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

REFRESH_INTERVAL_HOURS = 24


async def _daily_refresh_loop():
    """Background task: refresh TLEs from CelesTrak every 24 hours."""
    while True:
        await asyncio.sleep(REFRESH_INTERVAL_HOURS * 3600)
        try:
            conn = connect()
            refresh(conn)
            conn.close()
        except Exception as e:
            logger.error("Daily TLE refresh failed: %s", e)


@asynccontextmanager
async def lifespan(app: FastAPI):
    # Startup: init DB and seed if empty
    conn = connect()
    init_db(conn)
    seed_if_empty(conn)
    conn.close()
    # Launch daily refresh in background
    task = asyncio.create_task(_daily_refresh_loop())
    yield
    # Shutdown
    task.cancel()


app = FastAPI(title='SatPredict Local API', version='0.1.0', lifespan=lifespan)
app.add_middleware(
    CORSMiddleware,
    allow_origins=['*'],
    allow_credentials=True,
    allow_methods=['*'],
    allow_headers=['*'],
)


@app.get('/api/health')
def health():
    conn = connect()
    try:
        count = conn.execute("SELECT COUNT(DISTINCT norad_id) FROM tle_records").fetchone()[0]
    finally:
        conn.close()
    return {'ok': True, 'satellites': count}


@app.post('/api/refresh')
def trigger_refresh():
    conn = connect()
    try:
        refresh(conn)
    finally:
        conn.close()
    return {'ok': True}


@app.get('/api/satellites')
def satellites(q: str = '', limit: int = Query(default=50, le=500)):
    conn = connect()
    try:
        return {'items': list_satellites(conn, q=q, limit=limit)}
    finally:
        conn.close()


@app.get('/api/tles/latest/{norad_id}')
def latest_tle(norad_id: int):
    conn = connect()
    try:
        rec = get_latest_tle(conn, norad_id)
        if not rec:
            raise HTTPException(status_code=404, detail='NORAD not found')
        return rec.__dict__
    finally:
        conn.close()


@app.get('/api/predict/overpass')
def predict_overpass(
    norad_id: int,
    target_lat: float,
    target_lon: float,
    start_date: str | None = None,
    predict_days: int = 1,
    sensor_model: str = 'pushbroom',
    max_offnadir_deg: float = 30.0,
):
    conn = connect()
    try:
        rec = get_latest_tle(conn, norad_id)
        if not rec:
            raise HTTPException(status_code=404, detail='NORAD not found')
    finally:
        conn.close()

    requested_date = date.fromisoformat(start_date) if start_date else date.today()
    if rec.epoch_utc:
        tle_epoch = datetime.fromisoformat(rec.epoch_utc.replace('Z', '+00:00')).date()
        if requested_date > (tle_epoch + timedelta(days=7)):
            requested_date = tle_epoch

    cfg = PredictionConfig(sensor_model=sensor_model, max_offnadir_deg=max_offnadir_deg)
    req = PredictionRequest(
        tle=TLE(name=rec.name, line1=rec.line1, line2=rec.line2, source=rec.source or 'sqlite'),
        target=Target(lat=target_lat, lon=target_lon, alt_m=0.0),
        start_date=requested_date,
        predict_days=predict_days,
        config=cfg,
    )
    out = Predictor().run(req)
    return {
        'norad_id': norad_id,
        'target': {'lat': target_lat, 'lon': target_lon},
        'sensor_model': sensor_model,
        'tle': {'line1': rec.line1, 'line2': rec.line2},
        'swath_km': cfg.swath_km,
        'passes': [out[k] for k in sorted(out.keys(), key=int)],
        'count': len(out),
    }


# --- Static file serving (must be last: catch-all at "/") ---
from fastapi.staticfiles import StaticFiles
from pathlib import Path

_web_dir = Path(__file__).resolve().parent.parent / "web"
app.mount("/", StaticFiles(directory=str(_web_dir), html=True), name="web")
