# SatPredict (Modernization WIP)

This repository modernizes the original `SatPredict.py` predictor into a package-first architecture with:

- clean I/O boundaries for TLE sources
- deterministic prediction engine wrapper
- future API-ready models

## Quick start

```bash
python -m venv .venv
source .venv/bin/activate
pip install -e .
satpredict --help
```

## Current status

- ✅ Legacy predictor preserved
- ✅ Package scaffold + CLI
- ✅ CelesTrak fetch + local TLE ZIP extraction utilities
- 🚧 Refactoring internals into stateless compute functions
- 🚧 API contract implementation
