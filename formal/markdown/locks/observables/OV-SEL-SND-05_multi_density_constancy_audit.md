# OV-SEL-SND-05 — Multi-density constancy audit (computed)

Scope / limits
- Bookkeeping / narrative only; no physics claim
- New mapping/constancy records are non-decisive by design; no selection/regime effects

Narrative (operational)

Multi-density constancy audit (bookkeeping-only; no physics claim):
1) What changed? Added a decision-gate coverage report, a cross-source mapping record (blocked), and an OV-SND-04 constancy-check scaffold.
2) What did not change? Selection/regime/policy locks are unchanged; new records are non-decisive by design.
3) Forbidden behaviors: no continuity inference; no regime averaging; no selection participation; no cross-source condition identity assumption.

Self-checks (lock==computed + negative token checks) all_ok=True.

Record (computed)

```json
{
  "checks": {
    "No OV-BR-SND-02 token in OV-SEL-01": {
      "lock_path": "formal/markdown/locks/observables/OV-SEL-01_selection_status.md",
      "ok": true,
      "token": "OV-BR-SND-02"
    },
    "No OV-BR-SND-02 token in OV-XD-04": {
      "lock_path": "formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison_DQ-01_v2.md",
      "ok": true,
      "token": "OV-BR-SND-02"
    },
    "No OV-SND-04 token in OV-SEL-01": {
      "lock_path": "formal/markdown/locks/observables/OV-SEL-01_selection_status.md",
      "ok": true,
      "token": "OV-SND-04"
    },
    "No OV-SND-04 token in OV-XD-04": {
      "lock_path": "formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison_DQ-01_v2.md",
      "ok": true,
      "token": "OV-SND-04"
    },
    "OV-BR-SND-02": {
      "lock_fingerprint": "365869bd6a3ea7b9a0f4afc43aaa234bae28bd289f55866f42b811ddf55c26e4",
      "lock_path": "formal/markdown/locks/observables/OV-BR-SND-02_cross_source_density_mapping.md",
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
    "OV-SND-03N-COV": {
      "lock_fingerprint": "10adc18eda47c61a65702abc6fc6f0f0dad76cb97601a33e4257fc54a95e6525",
      "lock_path": "formal/markdown/locks/observables/OV-SND-03N_density_coverage_report.md",
      "ok": true
    },
    "OV-SND-04": {
      "lock_fingerprint": "c7a0c4f14e3a3bb32f58f41ab0d277fc0c7f81e7f781d5cb1e35e21338c0f95f",
      "lock_path": "formal/markdown/locks/observables/OV-SND-04_sound_speed_density_constancy.md",
      "ok": true
    }
  },
  "fingerprint": "04f5baf71665fb748578652736d85300a1eb9fb8079476469f30cdacb9599127",
  "narrative": "Multi-density constancy audit (bookkeeping-only; no physics claim):\n1) What changed? Added a decision-gate coverage report, a cross-source mapping record (blocked), and an OV-SND-04 constancy-check scaffold.\n2) What did not change? Selection/regime/policy locks are unchanged; new records are non-decisive by design.\n3) Forbidden behaviors: no continuity inference; no regime averaging; no selection participation; no cross-source condition identity assumption.\n\nSelf-checks (lock==computed + negative token checks) all_ok=True.",
  "schema": "OV-SEL-SND-05_multi_density_constancy_audit/v1",
  "status_date": "2026-01-24"
}
```

Record fingerprint: `04f5baf71665fb748578652736d85300a1eb9fb8079476469f30cdacb9599127`
