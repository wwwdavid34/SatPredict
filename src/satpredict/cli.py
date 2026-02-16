from __future__ import annotations

import argparse
from datetime import date
from pprint import pprint

from .engine import Predictor, PredictionConfig, PredictionRequest
from .models import Target
from .sources import fetch_celestrak_group, load_tles_from_zip


def main() -> None:
    parser = argparse.ArgumentParser(description="SatPredict modernization CLI")
    parser.add_argument("--lat", type=float, required=True)
    parser.add_argument("--lon", type=float, required=True)
    parser.add_argument("--date", type=str, default=date.today().isoformat())
    parser.add_argument("--days", type=int, default=1)
    parser.add_argument("--group", type=str, default="stations", help="CelesTrak group")
    parser.add_argument("--zip", type=str, help="Path to TLE ZIP file")
    parser.add_argument("--index", type=int, default=0, help="Pick nth TLE from source")
    parser.add_argument("--coarse-step-seconds", type=float, default=120.0)
    parser.add_argument("--iteration-limit", type=int, default=1000)
    parser.add_argument("--swath-km", type=float, default=3000.0)
    parser.add_argument("--bearing-precision-deg", type=float, default=0.0001)
    parser.add_argument("--min-step-seconds", type=float, default=0.005)
    parser.add_argument("--max-stall-iterations", type=int, default=30)
    args = parser.parse_args()

    if args.zip:
        tles = load_tles_from_zip(args.zip, limit=max(1000, args.index + 1))
    else:
        tles = fetch_celestrak_group(args.group)

    if not tles:
        raise SystemExit("No TLEs found from selected source")
    if args.index >= len(tles):
        raise SystemExit(f"index {args.index} out of range ({len(tles)} TLEs)")

    req = PredictionRequest(
        tle=tles[args.index],
        target=Target(lat=args.lat, lon=args.lon, alt_m=0),
        start_date=date.fromisoformat(args.date),
        predict_days=args.days,
        config=PredictionConfig(
            coarse_step_seconds=args.coarse_step_seconds,
            iteration_limit=args.iteration_limit,
            swath_km=args.swath_km,
            bearing_precision_deg=args.bearing_precision_deg,
            min_step_seconds=args.min_step_seconds,
            max_stall_iterations=args.max_stall_iterations,
        ),
    )

    result = Predictor().run(req)
    pprint(result)


if __name__ == "__main__":
    main()
