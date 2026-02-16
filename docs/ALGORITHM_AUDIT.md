# Overpass Algorithm Audit (Paper ↔ Implementation)

Project: `SatPredict-modernize`
Reference paper: Hsu et al., Remote Sensing 2019, 11, 995 (`remotesensing-11-00995.pdf`)

## 1) Paper flow (Section 2.2) distilled

1. Pick seed location/time.
2. Load closest TLE to seed time.
3. Propagate coarsely (paper says 10 min) to detect candidate overpass.
4. Reverse direction, reduce step by 10× repeatedly.
5. Converge when scan-plane visibility angle change < 0.0001°.
6. Advance seed by 60 min and repeat for 24 h.
7. Interpolate vessel location at predicted overpass time.
8. Skip interpolation if overpass is >2 h from neighboring VMS records.

---

## 2) Where this lives in legacy code

- **Daily loop / pass list over horizon:** `_run_predict` (line ~292)
- **Overpass solver core:** `predict` (line ~430)
- **Single-epoch propagation:** `propogate` (line ~366)
- **Geometry/conversion helpers:** `_geo2eci`, `_eci2geo`, `_getAng`, `_getVec`, etc. (lines ~651+)
- **Optional timing correction:** `_applyCorrection` (line ~584)

---

## 3) Paper-vs-code differences (important)

### A. Refinement factor differs
- Paper narrative: reduce timestep by **10×** each refinement stage.
- Code: when `(passedObs and visible)` then `tspan = tspan / (-20.)`.
- Impact: behavior still converges, but algorithm semantics differ from publication.

### B. Coarse step differs
- Paper narrative: coarse propagation at 10 min.
- Code default: `tspanDef = 120` sec (2 min).
- Impact: generally fine (more robust for short passes), but should be documented as intentional divergence.

### C. TLE refresh path is network-coupled
- `_run_predict` may call `get_satrec()` if TLE epoch drift threshold crossed.
- Legacy `get_satrec()` relies on old EOG API endpoint.
- Impact: brittle in offline/modern environments.
- Mitigation already added in modernization wrapper: inject satrec + bypass network refresh.

### D. Timing correction polynomial mismatch (high-risk)
- Comment says term is `-9.61E-2 * X`.
- Code implements `-9.61 * lat` (100× larger coefficient):
  ```python
  cor=7e-8*lat**4+2e-5*lat**3-3e-4*lat**2-9.61*lat-0.7046
  ```
- Impact: potentially large systematic time correction bias depending on latitude.
- Recommendation: verify original regression source and fix under guarded feature flag + regression tests.

### E. Numerical robustness risk in angle ops
- `_getAng()` uses raw `acos(dot/(|a||b|))` with no clamp to [-1,1].
- Impact: occasional domain errors due to floating-point rounding near boundaries.
- Recommendation: clamp cosine argument before `acos`.

### F. Legacy state/global coupling
- Class initializes from module-level globals.
- Inputs/outputs mix UTC/local strings + Julian + mutable state.
- Impact: hard to test and reason about determinism.

---

## 4) What appears scientifically aligned

- SGP4-based propagation logic is present and central.
- Visibility uses swath-distance check and crossing logic.
- Iterative convergence to boundary condition is implemented.
- Repeated pass search over horizon is implemented by stepping forward from previous event.

---

## 5) Code cleanup plan (recommended order)

## Phase 1 — Stabilize behavior (no science changes)
1. Freeze legacy behavior with golden tests from known date/location/TLE fixtures.
2. Isolate side effects (no network in core compute path).
3. Replace print-based diagnostics with structured logger.
4. Add explicit dataclasses for inputs/outputs.

## Phase 2 — Numerical hardening
1. Add safe clamp in all acos paths.
2. Add explicit convergence tolerance constants.
3. Document/refactor timestep strategy (2 min + /20 vs paper /10), keep configurable.
4. Add edge-case tests: dateline crossing, near-pole, short passes, no-pass window.

## Phase 3 — Scientific reconciliation
1. Reproduce paper baseline with archived TLE/VMS/VNF slice.
2. Validate correction polynomial coefficient (`-9.61e-2` vs `-9.61`).
3. Decide canonical algorithm spec for v1.0 and lock in docs.

## Phase 4 — Architecture modernization
1. Keep `engine` stateless.
2. Move parsers to adapters (`TLE`, `OMM`, future formats).
3. Keep API contract independent of source format.
4. Add benchmark + error dashboard (P50/P95 timing deltas vs VNF).

---

## 6) Immediate actionable tasks (next coding sprint)

1. Add `tests/test_predict_golden.py` with 3 fixed scenarios.
2. Add `math_utils.safe_acos()` and route `_getAng()` through it.
3. Make refinement params configurable:
   - `coarse_step_seconds`
   - `refine_factor`
   - `bearing_precision_deg`
4. Add `--source-format` plumbing scaffold in CLI for future OMM.

---

## 7) Validation status snapshot

Using latest local VNF (`VNF_npp_d20260216_noaa_v30.csv.gz`) with matching date:
- Predicted: `2026-02-16T03:14:55Z`
- Nearest VNF: `2026-02-16T03:14:55.796Z`
- Delta: `0.796 s`

This indicates the core timing behavior can be very close when epoch alignment is appropriate.
