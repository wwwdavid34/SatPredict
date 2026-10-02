# 3D Earth Globe Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Replace the MVP HTML page with a full-viewport CesiumJS globe showing day/night rendering, satellite ground tracks, and swath footprints for predicted overpasses.

**Architecture:** CesiumJS loaded via CDN in a single vanilla HTML/JS page. Controls overlaid as CSS panels. Client-side orbit propagation from TLE data returned by the API. FastAPI serves the page via StaticFiles mount.

**Tech Stack:** CesiumJS (CDN), satellite.js (CDN), vanilla HTML/JS/CSS, existing FastAPI backend

---

### Task 1: Add TLE and swath data to API response

**Files:**
- Modify: `app_local/api/main.py:55-93` (predict_overpass endpoint)
- Create: `tests/test_api_response.py`

**Step 1: Write the failing test**

Create `tests/test_api_response.py`:

```python
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
```

**Step 2: Run test to verify it fails**

Run: `conda run -n satpredict pytest tests/test_api_response.py -v`
Expected: FAIL — response does not contain `tle` or `swath_km` keys

**Step 3: Add TLE and swath_km to the response**

In `app_local/api/main.py`, modify the `predict_overpass` function. Store `cfg = req.config` before calling `Predictor().run(req)`, then change the return dict to:

```python
    cfg = req.config
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
```

**Step 4: Run test to verify it passes**

Run: `conda run -n satpredict pytest tests/test_api_response.py -v`
Expected: PASS (or skip if no TLE data)

**Step 5: Commit**

```bash
git add app_local/api/main.py tests/test_api_response.py
git commit -m "Add TLE and swath_km to overpass API response for client-side orbit rendering"
```

---

### Task 2: Serve the web directory via FastAPI StaticFiles

**Files:**
- Modify: `app_local/api/main.py` (add StaticFiles mount at bottom)

**Step 1: Add StaticFiles mount**

Add at the bottom of `main.py` (after all route definitions):

```python
from fastapi.staticfiles import StaticFiles
from pathlib import Path

_web_dir = Path(__file__).resolve().parent.parent / "web"
app.mount("/", StaticFiles(directory=str(_web_dir), html=True), name="web")
```

**Step 2: Verify manually**

Run: `curl -s http://localhost:8000/ | head -5`
Expected: HTML content from `index.html`

**Step 3: Commit**

```bash
git add app_local/api/main.py
git commit -m "Mount web directory as static files at root for single-server dev"
```

---

### Task 3: CesiumJS globe with day/night rendering, track, and swath

**Files:**
- Rewrite: `app_local/web/index.html`

This is the main task. Replace the entire `index.html` with the CesiumJS globe page. Key requirements:

- Full-viewport CesiumJS globe with `enableLighting = true` for day/night
- Collapsible left sidebar panel with: satellite search, target lat/lon, date, sensor model, off-nadir angle, predict button
- Pass list panel: clickable items showing time, off-nadir angle, distance, altitude
- Click-to-set target on globe (bidirectional sync with lat/lon inputs)
- satellite.js loaded from CDN for client-side SGP4 orbit propagation

**Important: Use safe DOM methods (createElement, textContent, appendChild) instead of innerHTML to avoid XSS.**

**Step 1: Write the globe HTML page**

Rewrite `app_local/web/index.html`. Structure:

**HTML structure:**
```
<div id="cesiumContainer"> — full viewport
<div id="controlPanel"> — overlaid left sidebar
  - Panel toggle button
  - Satellite search input + button + select dropdown
  - Lat/Lon number inputs (inline row)
  - Date input (type=date, default today)
  - Sensor select + off-nadir input (inline row)
  - Predict button
  - #passList div for dynamically-added pass items
  - #status div for messages
```

**CSS:**
```
- Body/html: 100% width/height, no margin, overflow hidden
- #cesiumContainer: 100% width/height
- #controlPanel: position absolute, top-left, 320px wide, dark semi-transparent background,
  backdrop-filter blur, border-radius 8px, z-index 10
- .collapsed class hides all children except toggle button
- Form inputs: full width, dark background, white text, subtle border
- .pass-item: clickable cards with hover/selected states
- button.primary: blue (#2563eb) with hover darken
```

**JavaScript globals:**
```javascript
const API = '/api';
let currentPasses = [];
let currentTLE = null;
let currentSwathKm = 3000;
let targetEntity = null;
let trackEntities = [];
```

**Cesium viewer config:**
```javascript
Cesium.Ion.defaultAccessToken = '<default Cesium Ion token>';
const viewer = new Cesium.Viewer('cesiumContainer', {
  terrainProvider: undefined,
  baseLayerPicker: false, geocoder: false, homeButton: false,
  sceneModePicker: false, navigationHelpButton: false,
  animation: false, timeline: false, fullscreenButton: false,
  vrButton: false, infoBox: false, selectionIndicator: false,
  shadows: false, shouldAnimate: false,
});
viewer.scene.globe.enableLighting = true;
```

**Click-to-set target:**
```javascript
// ScreenSpaceEventHandler on LEFT_CLICK
// pickEllipsoid -> Cartographic -> update lat/lon inputs + placeTarget()
```

**placeTarget(lat, lon):**
```javascript
// Remove old targetEntity if exists
// Add point entity (yellow, 10px) with "Target" label
```

**loadSats():**
```javascript
// Fetch /api/satellites, populate <select> dropdown using createElement/textContent
```

**predict():**
```javascript
// Read form values, call /api/predict/overpass
// Store response passes, tle, swath_km
// Render pass list, auto-select first pass
```

**renderPassList():**
```javascript
// Clear #passList
// For each pass: createElement('div'), set className 'pass-item'
// Create child elements with textContent (not innerHTML) for:
//   - "Pass N: <timeEndLOC>" (bold)
//   - "Off-nadir: X° · Dist: Y km · Alt: Z km" (details)
// Attach onclick -> selectPass(i)
```

**selectPass(idx):**
```javascript
// Highlight selected pass-item
// Parse Julian date from pass.timeEndUTC -> JS Date -> Cesium.JulianDate
//   JD 2451545.0 = 2000-01-01T12:00:00Z, convert via ms offset
// Set viewer.clock.currentTime, shouldAnimate = false
// Call renderOrbit(pass)
// Call updateTerminator()
```

**renderOrbit(pass):**
```javascript
// Clear trackEntities
// If satellite.js not loaded, dynamically load from CDN, then call renderOrbitWithSgp4
// Otherwise call renderOrbitWithSgp4 directly
```

**renderOrbitWithSgp4(pass, centerDate, halfPeriodSec):**
```javascript
// twoline2satrec from currentTLE
// Parse mean motion from TLE line2[52:63] to get orbital period
// halfPeriodSec = (1440/meanMotion * 60) / 2
// Sample positions every 30 seconds for one full orbit centered on pass time
// For each sample: propagate -> eciToGeodetic -> {lon, lat, alt, time}

// Split positions at antimeridian crossings (|lon_delta| > 180)

// Ground track: cyan polyline per segment, width 2, clampToGround
// Swath corridor: for each segment, compute perpendicular offsets at swathHalfDeg = (swath_km/2)/111.32
//   - For each point, compute bearing to next point
//   - Offset left/right perpendicular to track
//   - Build polygon: left coords forward + right coords reversed
//   - Material: cyan with 0.12 alpha, outline cyan 0.3 alpha

// Satellite position marker: red point at closest sample to pass time, labeled "SAT"

// Fly camera to oblique view
```

**flyToObliqueView(tgtLat, tgtLon, satPos):**
```javascript
// Compute bearing from target to satellite position
// Place camera ~8° opposite the approach direction
// flyTo with altitude 2,500,000m, heading toward satellite, pitch -55° (35° above horizon)
// Duration 1.5s
```

**Geometry helpers needed:**
- `getBearing(lat1, lon1, lat2, lon2)` — bearing in degrees
- `offsetPoint(lat, lon, distDeg, bearingDeg)` — returns {lat, lon}
- `splitAtAntimeridian(positions)` — returns array of segments

**Step 2: Verify manually in browser**

1. Open `http://localhost:8000/` — full-viewport globe with day/night shading
2. Click globe — yellow target pin, lat/lon fields update
3. Search "25544" — ISS in dropdown
4. Click Predict — passes listed in panel
5. Click a pass — clock updates, day/night shifts, cyan orbit track + swath ribbon shown, red SAT marker
6. Camera flies to oblique view

**Step 3: Commit**

```bash
git add app_local/web/index.html
git commit -m "Replace MVP page with CesiumJS 3D globe, day/night, track and swath rendering"
```

---

### Task 4: Add terminator line for day/night boundary

**Files:**
- Modify: `app_local/web/index.html` (add updateTerminator function)

**Step 1: Add terminator computation**

Add `updateTerminator()` function that:
1. Removes previous terminator entity if it exists
2. Computes sub-solar point from `Cesium.Simon1994PlanetaryPositions.computeSunPositionInEarthInertialFrame`
3. Transforms from inertial to fixed frame via `Cesium.Transforms.computeTemeToPseudoFixedMatrix`
4. Computes 360 points on the great circle 90° from sub-solar point:
   ```
   For azimuth 0..360:
     lat = asin(sin(subSolarLat)*cos(π/2) + cos(subSolarLat)*sin(π/2)*cos(az))
     lon = subSolarLon + atan2(sin(az)*sin(π/2)*cos(subSolarLat), cos(π/2)-sin(subSolarLat)*sin(lat))
   ```
5. Adds orange polyline entity (width 2, alpha 0.6, clampToGround)

Call `updateTerminator()` inside `selectPass()` after setting the clock time.

**Step 2: Verify manually**

Select a pass — orange terminator line should appear at the day/night boundary on the globe.

**Step 3: Commit**

```bash
git add app_local/web/index.html
git commit -m "Add solar terminator line to globe at predicted pass time"
```

---

### Task 5: End-to-end verification

**Step 1: Run existing tests**

```bash
conda run -n satpredict pytest tests/ -v --timeout=60
```

Expected: All existing tests pass, new test_api_response passes.

**Step 2: Manual verification checklist**

1. `http://localhost:8000/` — globe loads, day/night visible
2. Click globe — target pin placed, lat/lon updated
3. Search "25544" — ISS appears in dropdown
4. Click Predict — passes listed
5. Click a pass — clock updates, day/night shifts, orbit track + swath + terminator shown
6. Camera flies to oblique ~35° view of target
7. Panel collapses/expands with toggle button
8. Changing lat/lon manually and predicting again works

**Step 3: Commit any fixes if needed**

---

## Execution Summary

| Task | What | Files |
|------|------|-------|
| 1 | Add TLE + swath_km to API response | `main.py`, new test |
| 2 | Mount static files for single-server dev | `main.py` |
| 3 | CesiumJS globe with track + swath | `index.html` (rewrite) |
| 4 | Terminator line | `index.html` (addition) |
| 5 | End-to-end verification | tests |
