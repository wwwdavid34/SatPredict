import { describe, it, expect } from "vitest";
import * as satellite from "satellite.js";
import { apiOmmToTleLines, omm2satrec, type ApiOmm } from "./tle-parse";

// satellite.js types `position` as `EciVec3<Kilometer> | boolean`, so a truthy
// check alone can't narrow away the `true` literal. This guard does.
function vec3(p: satellite.EciVec3<number> | boolean): satellite.EciVec3<number> {
  if (typeof p === "boolean") throw new Error("expected position vector");
  return p;
}

// Real ISS OMM captured from the API (numeric fields, uppercase names).
const ISS_OMM: ApiOmm = {
  OBJECT_NAME: "ISS (ZARYA)",
  OBJECT_ID: "1998-067A",
  NORAD_CAT_ID: 25544,
  EPOCH: "2026-05-14T15:36:11.376288",
  MEAN_MOTION: 15.49215603,
  ECCENTRICITY: 0.00075141,
  INCLINATION: 51.6311,
  RA_OF_ASC_NODE: 106.1165,
  ARG_OF_PERICENTER: 58.4526,
  MEAN_ANOMALY: 301.7195,
  BSTAR: 9.5926049e-5,
  MEAN_MOTION_DOT: 4.878e-5,
  MEAN_MOTION_DDOT: 0.0,
  REV_AT_EPOCH: 56655,
  CLASSIFICATION_TYPE: "U",
  ELEMENT_SET_NO: 999,
  OBJECT_TYPE: "PAYLOAD",
};

describe("apiOmmToTleLines", () => {
  it("synthesizes TLE lines that represent the same orbit as omm2satrec", () => {
    const lines = apiOmmToTleLines(ISS_OMM);
    expect(lines).not.toBeNull();
    if (!lines) return;

    const fromTle = satellite.twoline2satrec(lines.line1, lines.line2);
    const fromOmm = omm2satrec(ISS_OMM);

    expect(fromTle.error).toBe(0);
    expect(fromOmm.error).toBe(0);

    const a = satellite.sgp4(fromTle, 60.0);
    const b = satellite.sgp4(fromOmm, 60.0);
    expect(a.position).toBeTruthy();
    expect(b.position).toBeTruthy();
    if (a.position && b.position) {
      const pa = vec3(a.position);
      const pb = vec3(b.position);
      // Within ~1 km on each axis.
      expect(pa.x).toBeCloseTo(pb.x, 0);
      expect(pa.y).toBeCloseTo(pb.y, 0);
      expect(pa.z).toBeCloseTo(pb.z, 0);
    }
  });

  it("returns null when NORAD ID doesn't fit the 5-char TLE field", () => {
    const highOmm: ApiOmm = { ...ISS_OMM, NORAD_CAT_ID: 270000 };
    expect(apiOmmToTleLines(highOmm)).toBeNull();
  });
});
