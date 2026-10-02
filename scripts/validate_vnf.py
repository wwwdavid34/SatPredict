#!/usr/bin/env python3
from __future__ import annotations

import argparse
from satpredict.validation import nearest_event_delta


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("vnf_csv")
    ap.add_argument("predicted_iso_utc")
    args = ap.parse_args()

    res = nearest_event_delta(args.vnf_csv, args.predicted_iso_utc)
    print(f"nearest_vnf={res.nearest_iso} delta_seconds={res.delta_seconds:.3f}")
