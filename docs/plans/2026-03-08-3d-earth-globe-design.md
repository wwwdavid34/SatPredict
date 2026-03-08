# 3D Earth Globe with Day/Night Rendering

## Summary

Replace the current minimal HTML MVP with a full-viewport CesiumJS globe as the primary interface. The globe shows day/night rendering at the predicted pass time, satellite ground track for one full orbit, and a swath footprint strip matching the sensor's field of view.

## Architecture

- Single-page vanilla HTML/JS app (no build tooling)
- CesiumJS loaded via CDN
- Globe fills the viewport; controls are overlaid panels
- Existing FastAPI backend unchanged except minor response additions

## UI Layout

- **Left sidebar** (collapsible): satellite search, target lat/lon inputs, date picker, sensor model selector, off-nadir angle, predict button
- **Full-screen CesiumJS globe**: main viewport behind panels
- **Pass list panel**: clickable list of predicted passes; selecting one updates globe time and camera

## Globe Features

### Day/Night Rendering
- Cesium scene lighting set to the selected pass's UTC timestamp
- Terminator line drawn on the globe surface for visual clarity

### Satellite Track
- One full orbit (~90 min) of ground track centered on the pass time
- Computed client-side from TLE using Cesium's built-in SGP4 propagator

### Swath Footprint
- Ground ribbon along the track matching the sensor's swath width
- Rendered as a corridor/polygon on the globe surface

### Target Marker
- Pin/point at the target location
- Set by clicking on the globe OR typing lat/lon (bidirectional sync)

### Camera
- Default view: oblique at ~35 deg elevation, oriented so the ground track crosses the view
- Auto-flies to frame the target + pass geometry when a pass is selected
- User can freely rotate/zoom from the default position

## Data Flow

1. User searches satellites via `GET /api/satellites`
2. User sets target by clicking globe or entering lat/lon
3. User clicks Predict -> `GET /api/predict/overpass`
4. Passes listed in panel; selecting one sets Cesium clock to that pass's timestamp
5. Track + swath computed client-side from TLE for the selected pass's orbit

## API Changes

- `GET /api/predict/overpass` response: add `tle` object (`{line1, line2}`) and `swath_km` (from sensor config) so the client can propagate the orbit and render the swath without additional API calls

## Decisions

- CesiumJS over Three.js/Globe.gl: purpose-built for geospatial + satellite visualization with built-in SGP4
- Vanilla JS (no React/Vue): matches existing project approach, no build tooling needed
- Client-side orbit propagation: avoids adding orbit-sampling endpoints to the API
- One full orbit track window: provides useful orbital context around each pass
- Oblique default camera (~35 deg): best balance of 3D effect, ground coverage visibility, and day/night rendering
