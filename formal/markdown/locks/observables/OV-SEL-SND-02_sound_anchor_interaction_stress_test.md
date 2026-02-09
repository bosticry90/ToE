# OV-SEL-SND-02 — Sound anchor interaction stress test (computed)

Scope / limits
- Bookkeeping / narrative only; no physics claim

Narrative (operational)

Sound anchor interaction stress test (bookkeeping-only; no physics claim):
Forbidden behaviors asserted absent:
- No benchmark or sound-anchor participation in selection/regime locks
- No cross-regime continuity inference or averaging
- Policy activation remains explicit and guarded

Self-checks (lock==computed + negative token checks) all_ok=False.

Record (computed)

```json
{
  "checks": {
    "No OV-BM in OV-SEL-01": {
      "lock_path": "formal/markdown/locks/observables/OV-SEL-01_selection_status.md",
      "ok": true,
      "token": "OV-BM-"
    },
    "No OV-SND in OV-SEL-01": {
      "lock_path": "formal/markdown/locks/observables/OV-SEL-01_selection_status.md",
      "ok": true,
      "token": "OV-SND-"
    },
    "No OV-SND in OV-XD-04": {
      "lock_path": "formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison_DQ-01_v2.md",
      "ok": true,
      "token": "OV-SND-"
    },
    "OV-BM-01": {
      "lock_fingerprint": "1ee5c6899cb28c404b2ab6c0ae79a6751a2363ddd5fc8b12c6acd0c9c44353b3",
      "lock_path": "formal/markdown/locks/benchmarks/OV-BM-01_mean_field_line_shift_scaling.md",
      "ok": true
    },
    "OV-BM-01N": {
      "lock_fingerprint": "bed12796e7427943b998f80ad5eb7de37dbcb26dd11c902e119b5a88b6210eb3",
      "lock_path": "formal/markdown/locks/benchmarks/OV-BM-01_mean_field_line_shift_scaling_digitized.md",
      "ok": false
    },
    "OV-BM-02": {
      "lock_fingerprint": "0e32eee80d2065f24f99ab1524c76cb5a8deeb7d4372ac9986651d75d5c38b4e",
      "lock_path": "formal/markdown/locks/benchmarks/OV-BM-02_linewidth_quadrature_composition.md",
      "ok": true
    },
    "OV-BM-02N": {
      "lock_fingerprint": "1521fc3190d43b74d09e68616618e6987afec354570a65fe997fc90cd238432c",
      "lock_path": "formal/markdown/locks/benchmarks/OV-BM-02_linewidth_quadrature_composition_digitized.md",
      "ok": true
    },
    "OV-BR-02 (DQ-01_v2)": {
      "lock_fingerprint": "f2acf9f426e580dcf9265b238b5d611344baed22c4061e8c5701a11dcfb54d32",
      "lock_path": "formal/markdown/locks/observables/OV-BR-02_regime_bridge_record_DQ-01_v2.md",
      "ok": true
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
    "OV-XD-03": {
      "lock_fingerprint": "e50a44d369d0ff9c4f56fc6756456df5ceaf9818a2632a6da56167ac551c674d",
      "lock_path": "formal/markdown/locks/observables/OV-XD-03_cross_dataset_overlap_band_record.md",
      "ok": true
    },
    "OV-XD-04 (DQ-01_v2)": {
      "lock_fingerprint": "a3e8603c2dcffa9d904c799a7349d328089ffc1bccf39a3e2a074bc83e92bf31",
      "lock_path": "formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison_DQ-01_v2.md",
      "ok": true
    }
  },
  "fingerprint": "0f2b93184fbc1879404f91b80e9f09e07b4879c8a6b2a564b0fce9444565447d",
  "narrative": "Sound anchor interaction stress test (bookkeeping-only; no physics claim):\nForbidden behaviors asserted absent:\n- No benchmark or sound-anchor participation in selection/regime locks\n- No cross-regime continuity inference or averaging\n- Policy activation remains explicit and guarded\n\nSelf-checks (lock==computed + negative token checks) all_ok=False.",
  "schema": "OV-SEL-SND-02_sound_anchor_interaction_stress_test/v1",
  "status_date": "2026-01-24"
}
```

Record fingerprint: `0f2b93184fbc1879404f91b80e9f09e07b4879c8a6b2a564b0fce9444565447d`
