const HOUR = 3600;
const DAY = 86400;

/** Cache max-age (seconds) for a given query kind. Isolated so freshness is easy to tune. */
export function cacheTtlSeconds(
  kind: "latest" | "search" | "historical",
  epochDate?: string
): number {
  if (kind === "search") return 1 * HOUR;
  if (kind === "latest") return 6 * HOUR;
  // historical: immutable if the requested date is comfortably in the past (>2 days),
  // otherwise it's effectively "current" and should refresh like latest.
  if (epochDate) {
    const reqMs = new Date(epochDate + "T00:00:00Z").getTime();
    if (Date.now() - reqMs > 2 * DAY * 1000) return 30 * DAY;
  }
  return 6 * HOUR;
}
