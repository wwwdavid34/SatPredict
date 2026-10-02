import { describe, it, expect } from "vitest";
import { cacheTtlSeconds } from "./cache-policy";

describe("cacheTtlSeconds", () => {
  it("search is cached ~1h", () => {
    expect(cacheTtlSeconds("search")).toBe(3600);
  });
  it("latest is cached ~6h", () => {
    expect(cacheTtlSeconds("latest")).toBe(21600);
  });
  it("historical (clearly past epoch) is cached long", () => {
    expect(cacheTtlSeconds("historical", "2020-01-01")).toBe(2592000); // 30d
  });
  it("historical near today falls back to the latest TTL", () => {
    const today = new Date().toISOString().slice(0, 10);
    expect(cacheTtlSeconds("historical", today)).toBe(21600);
  });
});
