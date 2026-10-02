import { describe, it, expect } from "vitest";
import * as satellite from "satellite.js";
import { omm2satrec, type ApiOmm } from "./tle-parse";

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

describe("omm2satrec", () => {
  it("matches twoline2satrec propagation for the equivalent TLE", () => {
    // Equivalent TLE for the same ISS element set.
    const l1 = "1 25544U 98067A   26134.65013167  .00004878  00000-0  95926-4 0  9995";
    const l2 = "2 25544  51.6311 106.1165 0007514  58.4526 301.7195 15.49215603566556";
    const fromTle = satellite.twoline2satrec(l1, l2);
    const fromOmm = omm2satrec(ISS_OMM);

    expect(fromOmm.error).toBe(0);
    // jdsatepoch must match to sub-second (the conversions share jday).
    expect(fromOmm.jdsatepoch).toBeCloseTo(fromTle.jdsatepoch, 6);

    // Propagate both 60 minutes past epoch; positions must agree closely.
    const a = satellite.sgp4(fromOmm, 60.0);
    const b = satellite.sgp4(fromTle, 60.0);
    expect(a.position).toBeTruthy();
    expect(b.position).toBeTruthy();
    if (a.position && b.position) {
      expect(a.position.x).toBeCloseTo(b.position.x, 1); // km, within ~0.1
      expect(a.position.y).toBeCloseTo(b.position.y, 1);
      expect(a.position.z).toBeCloseTo(b.position.z, 1);
    }
  });

  it("handles NORAD > 99,999 (no 5-char TLE field involved)", () => {
    const highOmm: ApiOmm = { ...ISS_OMM, NORAD_CAT_ID: 270000, OBJECT_NAME: "HIGH ID TEST" };
    const satrec = omm2satrec(highOmm);
    expect(satrec.error).toBe(0);
    const g = satellite.sgp4(satrec, 10.0);
    expect(g.position).toBeTruthy();
  });

  it("parses an EPOCH string that already has a Z suffix", () => {
    const satrec = omm2satrec({ ...ISS_OMM, EPOCH: "2026-08-31T20:28:48.860256Z" });
    expect(satrec.error).toBe(0);
    expect(Number.isFinite(satrec.jdsatepoch)).toBe(true);
  });
});
