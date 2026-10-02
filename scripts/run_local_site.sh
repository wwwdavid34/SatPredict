#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

CONDA=/home/david/miniconda3/bin/conda
PYTHONPATH=. $CONDA run -n satpredict python scripts/ingest_tles_sqlite.py --year-filter 2025 --max-records 200000

echo "Starting API on http://127.0.0.1:8000"
PYTHONPATH=. $CONDA run -n satpredict uvicorn app_local.api.main:app --host 127.0.0.1 --port 8000
