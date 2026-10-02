export interface Env {
  ORBITAL_API_KEY: string;
}

export interface SatelliteSearchResult {
  norad_id: number;
  name: string;
  object_type: string | null;
  epoch_utc: string | null;
}

export interface PredictionConfig {
  coarseStepSeconds: number;
  iterationLimit: number;
  swathKm: number;
  bearingPrecisionDeg: number;
  minStepSeconds: number;
  maxStallIterations: number;
  maxOffnadirDeg: number;
}

export interface PassResult {
  id: number;
  satLat: number;
  satLon: number;
  satAlt: number;
  scanAngle: number;
  distance: number;
  bearing: number;
  timeEndUTC: string;
  timeEndLOC: string;
  timeEndUTC_J: number;
  timeEndLOC_J: number;
  timeIniUTC_J: number;
  exitReason: string;
  dayNight: number;
  ascending: number;
  solarElevation?: number;
  sensor_model: string;
  observable: boolean;
}

export interface PredictionResult {
  passes: Record<string, PassResult>;
  reachable: boolean;
  max_latitude_deg?: number;
  inclination_deg?: number;
  offnadir_margin_deg?: number;
  apogee_alt_km?: number;
  reason?: string;
}

export const DEFAULT_CONFIG: PredictionConfig = {
  coarseStepSeconds: 120.0,
  iterationLimit: 1000,
  swathKm: 3000.0,
  bearingPrecisionDeg: 0.0001,
  minStepSeconds: 0.005,
  maxStallIterations: 30,
  maxOffnadirDeg: 55.0,
};
