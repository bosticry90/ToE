# OV-SEL-SND-04 — Density dependence audit (computed)

Scope / limits
- Bookkeeping / narrative only; no physics claim
- New density artifacts are non-decisive by design; no selection/regime effects

Narrative (operational)

Density dependence audit (bookkeeping-only; no physics claim):
1) What changed? Added SND-DIG-01 policy, OV-SND-03N (digitized central density), and OV-SND-03 (density-scaled derived quantities).
2) What did not change? Selection/regime/policy locks are unchanged; new sound-lane density artifacts are non-decisive by design.
3) Forbidden behaviors: no continuity inference; no regime averaging; no selection participation.
4) Limitation: single-condition density anchor only; constancy across densities not tested here.

Self-checks (lock==computed + file existence + negative token checks) all_ok=True.

Record (computed)

```json
{
  "checks": {
    "No OV-SND-03 token in OV-SEL-01": {
      "lock_path": "formal/markdown/locks/observables/OV-SEL-01_selection_status.md",
      "ok": true,
      "token": "OV-SND-03"
    },
    "No OV-SND-03 token in OV-XD-04": {
      "lock_path": "formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison_DQ-01_v2.md",
      "ok": true,
      "token": "OV-SND-03"
    },
    "No OV-SND-03N token in OV-SEL-01": {
      "lock_path": "formal/markdown/locks/observables/OV-SEL-01_selection_status.md",
      "ok": true,
      "token": "OV-SND-03N"
    },
    "No OV-SND-03N token in OV-XD-04": {
      "lock_path": "formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison_DQ-01_v2.md",
      "ok": true,
      "token": "OV-SND-03N"
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
    "OV-SND-02": {
      "lock_fingerprint": "1e1e1f09907117e081fb9be9cab34d39884cf66acc8e2811d807e0a2db7a1dbe",
      "lock_path": "formal/markdown/locks/observables/OV-SND-02_sound_speed_from_propagation.md",
      "ok": true
    },
    "OV-SND-03": {
      "lock_fingerprint": "37803d75828ce358ef3afaf040bf2d3d44385db797294b8b6c9e94762ce4211a",
      "lock_path": "formal/markdown/locks/observables/OV-SND-03_sound_speed_density_scaling.md",
      "ok": true
    },
    "OV-SND-03N": {
      "lock_fingerprint": "d5222e1b706c3c8455e3c0e04f23e14473a04ab2dcff64ba13f266270f8eae7a",
      "lock_path": "formal/markdown/locks/observables/OV-SND-03_central_density_digitized.md",
      "ok": true
    },
    "OV-SND-03N CSV exists": {
      "exists": true,
      "path": "formal/external_evidence/bec_sound_andrews_1997/ovsnd03_density_digitization/central_density.csv"
    },
    "OV-SND-03N metadata exists": {
      "exists": true,
      "path": "formal/external_evidence/bec_sound_andrews_1997/ovsnd03_density_digitization/central_density.metadata.json"
    },
    "SND-DIG-01": {
      "lock_fingerprint": "3e2879d90d82ba8b420d39538a9b8b609cd5d1f52f8cac41de43fefdb294f973",
      "lock_path": "formal/markdown/locks/policies/SND-DIG-01_minimal_density_digitization.md",
      "ok": true
    }
  },
  "fingerprint": "45b29394a292b970ecc0f00c24371104bd652ff7972866b448060d859be99007",
  "narrative": "Density dependence audit (bookkeeping-only; no physics claim):\n1) What changed? Added SND-DIG-01 policy, OV-SND-03N (digitized central density), and OV-SND-03 (density-scaled derived quantities).\n2) What did not change? Selection/regime/policy locks are unchanged; new sound-lane density artifacts are non-decisive by design.\n3) Forbidden behaviors: no continuity inference; no regime averaging; no selection participation.\n4) Limitation: single-condition density anchor only; constancy across densities not tested here.\n\nSelf-checks (lock==computed + file existence + negative token checks) all_ok=True.",
  "schema": "OV-SEL-SND-04_density_dependence_audit/v1",
  "status_date": "2026-01-24"
}
```

Record fingerprint: `45b29394a292b970ecc0f00c24371104bd652ff7972866b448060d859be99007`
