# Local Website + SQLite API (Phase 1)

## What this gives you
- Local SQLite satellite TLE store
- FastAPI backend for site demos
- Local static web page for search + overpass prediction
- Sensor model toggle (`pushbroom` / `offnadir`)

## Data source
- Primary local source: `~/Downloads/TLEs.zip`
- Ingestion script supports nested yearly zip files.

## 1) Ingest satellites into SQLite
```bash
cd ~/Document/projects/SatPredict-modernize
PYTHONPATH=. /home/david/miniconda3/bin/conda run -n satpredict \
  python scripts/ingest_tles_sqlite.py --year-filter 2025 --max-records 200000
```

DB path:
- `data/satpredict.db`

## 2) Run API
```bash
cd ~/Document/projects/SatPredict-modernize
PYTHONPATH=. /home/david/miniconda3/bin/conda run -n satpredict \
  uvicorn app_local.api.main:app --host 127.0.0.1 --port 8000
```

API endpoints:
- `GET /api/health`
- `GET /api/satellites?q=<query>&limit=<n>`
- `GET /api/tles/latest/{norad_id}`
- `GET /api/predict/overpass?...`

## 3) Open local site
In another terminal:
```bash
cd ~/Document/projects/SatPredict-modernize/app_local/web
python3 -m http.server 5173
```

Then open:
- `http://127.0.0.1:5173/index.html`

The page points to API at `http://127.0.0.1:8000/api`.

## Notes
- For stale TLE requests, API auto-clamps requested date close to TLE epoch to avoid dead loops.
- This is local-first architecture; persistence/API contracts are AWS-migration-friendly.
