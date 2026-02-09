# OV-SEL-SND-03 — Derived sound-speed audit (computed)

Scope / limits
- Bookkeeping / narrative only; no physics claim
- OV-SND-02 is non-decisive by design; no selection/regime effects

Narrative (operational)

Derived sound-speed audit (bookkeeping-only; no physics claim):
1) What changed? Added OV-SND-02 as a derived sound-speed observable computed from frozen OV-SND-01N points under a pinned slope rule.
2) What did not change? Selection/regime/policy locks are unchanged; OV-SND-02 is non-decisive by design.
3) Forbidden behaviors: no continuity inference; no averaging across regimes; no benchmark/anchor participation in selection.

Self-checks (lock==computed + file existence + negative token checks) all_ok=True.

Record (computed)

```json
{
  "checks": {
    "No OV-SND-02 token in OV-SEL-01": {
      "lock_path": "formal/markdown/locks/observables/OV-SEL-01_selection_status.md",
      "ok": true,
      "token": "OV-SND-02"
    },
    "No OV-SND-02 token in OV-XD-04": {
      "lock_path": "formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison_DQ-01_v2.md",
      "ok": true,
      "token": "OV-SND-02"
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
    "OV-SND-01": {
      "lock_fingerprint": "fd28690a5df536f9bbf17602e3ce28f5b35245dfb6bc2b80769279e4a5e6cbbf",
      "lock_path": "formal/markdown/locks/observables/OV-SND-01_sound_speed_scaling_anchor.md",
      "ok": true
    },
    "OV-SND-01N": {
      "lock_fingerprint": "adfb63b0dbd71622df7670196f3646e0ec053eacd271b66079762a9122ce3530",
      "lock_path": "formal/markdown/locks/observables/OV-SND-01_sound_propagation_distance_time_digitized.md",
      "ok": true
    },
    "OV-SND-01N CSV exists": {
      "exists": true,
      "path": "formal/external_evidence/bec_sound_andrews_1997/ovsnd01_digitization/distance_vs_time_squares.csv"
    },
    "OV-SND-01N metadata exists": {
      "exists": true,
      "path": "formal/external_evidence/bec_sound_andrews_1997/ovsnd01_digitization/distance_vs_time_squares.metadata.json"
    },
    "OV-SND-02": {
      "lock_fingerprint": "1e1e1f09907117e081fb9be9cab34d39884cf66acc8e2811d807e0a2db7a1dbe",
      "lock_path": "formal/markdown/locks/observables/OV-SND-02_sound_speed_from_propagation.md",
      "ok": true
    }
  },
  "fingerprint": "8015c9da6ac036e6121939b9547e642fa6bb828c4e5bd4a7ca6cd9a3cb61bc69",
  "narrative": "Derived sound-speed audit (bookkeeping-only; no physics claim):\n1) What changed? Added OV-SND-02 as a derived sound-speed observable computed from frozen OV-SND-01N points under a pinned slope rule.\n2) What did not change? Selection/regime/policy locks are unchanged; OV-SND-02 is non-decisive by design.\n3) Forbidden behaviors: no continuity inference; no averaging across regimes; no benchmark/anchor participation in selection.\n\nSelf-checks (lock==computed + file existence + negative token checks) all_ok=True.",
  "schema": "OV-SEL-SND-03_sound_speed_derived_audit/v1",
  "status_date": "2026-01-24"
}
```

Record fingerprint: `8015c9da6ac036e6121939b9547e642fa6bb828c4e5bd4a7ca6cd9a3cb61bc69`
