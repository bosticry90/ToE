# OV-SEL-SND-01 — Sound anchor ingestion audit (computed)

Scope / limits
- Bookkeeping / narrative only; no physics claim
- Anchor ingestion is non-decisive by design; no selection/regime effects

Narrative (operational)

Sound anchor ingestion audit (bookkeeping-only; no physics claim):
1) What changed? Added OV-SND-01 (symbolic scaling anchor) and OV-SND-01N (minimal digitized distance-vs-time series) with pinned artifacts and computed locks.
2) What did not change? No selection/regime bookkeeping locks changed; no benchmarks or anchors participate in selection unless explicitly activated.
3) Why? OV-SND-01/01N are scope-fenced as non-decisive ingestion objects.

Self-checks (lock==computed + file existence) all_ok=True.

Record (computed)

```json
{
  "anchor": {
    "benchmark_only": true,
    "digitization_id": "OV-SND-01N",
    "digitized_csv_relpath": "formal/external_evidence/bec_sound_andrews_1997/ovsnd01_digitization/distance_vs_time_squares.csv",
    "digitized_csv_sha256": "2b1b2c77b106e474ffd80b48e977fb6ff6b988036e2e75fdabc82e93a8391021",
    "digitized_lock_path": "formal/markdown/locks/observables/OV-SND-01_sound_propagation_distance_time_digitized.md",
    "observable_id": "OV-SND-01",
    "symbolic_lock_path": "formal/markdown/locks/observables/OV-SND-01_sound_speed_scaling_anchor.md"
  },
  "checks": {
    "No OV-SND token in OV-SEL-01": {
      "lock_path": "formal/markdown/locks/observables/OV-SEL-01_selection_status.md",
      "ok": true,
      "token": "OV-SND-"
    },
    "No OV-SND token in OV-XD-04": {
      "lock_path": "formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison_DQ-01_v2.md",
      "ok": true,
      "token": "OV-SND-"
    },
    "OV-DQ-03": {
      "lock_fingerprint": "1d286352547eb0d547c85adeaeeceeb4b092ceb73981e9b20ad07825c4bf298e",
      "lock_path": "formal/markdown/locks/policies/DQ-01_active_policy_activation.md",
      "ok": true
    },
    "OV-SEL-01": {
      "lock_fingerprint": "14c4c9d4c49bf9f89c2f9f5e3418439d129b98e70f1d0b4d6006e5ed4f2cd5ed",
      "lock_path": "formal/markdown/locks/observables/OV-SEL-01_selection_status.md",
      "ok": true
    },
    "OV-SEL-02": {
      "lock_fingerprint": "b1c55cab148727c9da2556ffe8d8a7cbe0dbd7304c373204cb57e12ca6d580ac",
      "lock_path": "formal/markdown/locks/observables/OV-SEL-02_selection_status_policy_compare.md",
      "ok": true
    },
    "OV-SND-01 lock": {
      "lock_fingerprint": "fd28690a5df536f9bbf17602e3ce28f5b35245dfb6bc2b80769279e4a5e6cbbf",
      "lock_path": "formal/markdown/locks/observables/OV-SND-01_sound_speed_scaling_anchor.md",
      "ok": true
    },
    "OV-SND-01N CSV exists": {
      "exists": true,
      "path": "formal/external_evidence/bec_sound_andrews_1997/ovsnd01_digitization/distance_vs_time_squares.csv"
    },
    "OV-SND-01N lock": {
      "lock_fingerprint": "adfb63b0dbd71622df7670196f3646e0ec053eacd271b66079762a9122ce3530",
      "lock_path": "formal/markdown/locks/observables/OV-SND-01_sound_propagation_distance_time_digitized.md",
      "ok": true
    },
    "OV-SND-01N metadata exists": {
      "exists": true,
      "path": "formal/external_evidence/bec_sound_andrews_1997/ovsnd01_digitization/distance_vs_time_squares.metadata.json"
    }
  },
  "fingerprint": "042fb82a431f412702578f5f9a984727ca3a87a339968737373e316b65597336",
  "narrative": "Sound anchor ingestion audit (bookkeeping-only; no physics claim):\n1) What changed? Added OV-SND-01 (symbolic scaling anchor) and OV-SND-01N (minimal digitized distance-vs-time series) with pinned artifacts and computed locks.\n2) What did not change? No selection/regime bookkeeping locks changed; no benchmarks or anchors participate in selection unless explicitly activated.\n3) Why? OV-SND-01/01N are scope-fenced as non-decisive ingestion objects.\n\nSelf-checks (lock==computed + file existence) all_ok=True.",
  "schema": "OV-SEL-SND-01_sound_anchor_ingestion_audit/v1",
  "status_date": "2026-01-24"
}
```

Record fingerprint: `042fb82a431f412702578f5f9a984727ca3a87a339968737373e316b65597336`
