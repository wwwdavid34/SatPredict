from __future__ import annotations

from dataclasses import dataclass
from datetime import date
from pathlib import Path
import importlib.util
import sys

from .models import TLE, Target


@dataclass(slots=True)
class PredictionRequest:
    tle: TLE
    target: Target
    start_date: date
    predict_days: int = 1


class Predictor:
    """Thin wrapper over legacy SatPredict class while refactor is in progress."""

    def __init__(self, repo_root: str | Path | None = None) -> None:
        self.repo_root = Path(repo_root or Path(__file__).resolve().parents[2])
        self._legacy_cls = self._load_legacy_class()

    def _load_legacy_class(self):
        path = self.repo_root / "SatPredict.py"
        if str(self.repo_root) not in sys.path:
            sys.path.insert(0, str(self.repo_root))
        spec = importlib.util.spec_from_file_location("satpredict_legacy", path)
        if not spec or not spec.loader:
            raise RuntimeError(f"Failed to load legacy module from {path}")
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        return mod.SatPredict

    def run(self, request: PredictionRequest):
        p = self._legacy_cls()
        # Bypass legacy online TLE fetch path; inject satrec directly.
        p.tleL1 = request.tle.line1
        p.tleL2 = request.tle.line2
        p.tleL1Input = None
        p.tleL2Input = None
        p.satrec = self._legacy_satrec(request.tle.line1, request.tle.line2)

        p.startDate = request.start_date.isoformat()
        p.predictDays = int(request.predict_days)
        p.verbose = False
        p.obsPos["lat"] = request.target.lat
        p.obsPos["lon"] = request.target.lon
        p.obsPos["alt"] = request.target.alt_m

        # Use internal compute entrypoint directly to avoid legacy network-coupled checks.
        from datetime import datetime

        start_dt = datetime.fromisoformat(request.start_date.isoformat())
        start_jt = p.date2jd(start_dt)
        return p._run_predict(p.satrec, start_jt, p.obsPos, p.predictDays, p.verbose)

    def _legacy_satrec(self, line1: str, line2: str):
        from sgp4 import io
        from sgp4.earth_gravity import wgs72

        return io.twoline2rv(line1, line2, wgs72)
