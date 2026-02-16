import gzip
from pathlib import Path

from satpredict.validation import nearest_event_delta


def test_nearest_event_delta_reads_gz_and_date_mscan(tmp_path: Path):
    p = tmp_path / "sample.csv.gz"
    rows = [
        "Date_Mscan,Lat_GMTCO,Lon_GMTCO",
        "2026/02/16 03:14:55.796,19.362112,-12.376776",
        "2026/02/16 05:00:00.000,10.0,10.0",
    ]
    with gzip.open(p, "wt", encoding="utf-8") as f:
        f.write("\n".join(rows) + "\n")

    res = nearest_event_delta(p, "2026-02-16T03:14:55Z")
    assert res.nearest_iso == "2026-02-16T03:14:55.796000Z"
    assert 0.79 < res.delta_seconds < 0.81
