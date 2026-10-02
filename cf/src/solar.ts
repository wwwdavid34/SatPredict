const DEG2RAD = Math.PI / 180.0;

/**
 * Approximate solar elevation angle (degrees) at a surface location.
 * Uses the simple "solar declination + hour angle" model (Spencer 1971).
 * Returns negative values when the sun is below the horizon.
 */
export function solarElevation(utcStr: string, lat: number, lon: number): number {
  const dt = new Date(utcStr.replace(" ", "T") + "Z");
  const start = new Date(Date.UTC(dt.getUTCFullYear(), 0, 1));
  const doy = Math.floor((dt.getTime() - start.getTime()) / 86400000) + 1;
  const hourUtc = dt.getUTCHours() + dt.getUTCMinutes() / 60.0 + dt.getUTCSeconds() / 3600.0;

  // Solar declination (Spencer, 1971)
  const gamma = (2.0 * Math.PI * (doy - 1)) / 365.0;
  const decl =
    0.006918 -
    0.399912 * Math.cos(gamma) +
    0.070257 * Math.sin(gamma) -
    0.006758 * Math.cos(2 * gamma) +
    0.000907 * Math.sin(2 * gamma) -
    0.002697 * Math.cos(3 * gamma) +
    0.00148 * Math.sin(3 * gamma);

  // Equation of time (minutes)
  const eqtime =
    229.18 *
    (0.000075 +
      0.001868 * Math.cos(gamma) -
      0.032077 * Math.sin(gamma) -
      0.014615 * Math.cos(2 * gamma) -
      0.04089 * Math.sin(2 * gamma));

  // Solar hour angle
  const solarTime = hourUtc * 60.0 + eqtime + 4.0 * lon;
  const ha = DEG2RAD * (solarTime / 4.0 - 180.0);

  const latR = DEG2RAD * lat;
  const elev = Math.asin(
    Math.sin(latR) * Math.sin(decl) + Math.cos(latR) * Math.cos(decl) * Math.cos(ha)
  );
  return elev * (180.0 / Math.PI);
}
