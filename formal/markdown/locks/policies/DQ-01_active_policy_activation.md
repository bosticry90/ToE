# OV-DQ-03 — DQ-01 active policy activation (computed policy lock)

Scope / limits
- Bookkeeping / policy posture only; no physics claim
- Activates a selection-policy label; keeps DQ-01_v1 pinned as baseline

Narrative (operational)

DQ-01 active policy activation (bookkeeping-only; no physics claim):
- Active policy: DQ-01_v2 (q_threshold=1.05).
- Baseline policy remains pinned: DQ-01_v1 (q_threshold=0.9).
- Effective status date for selection narratives: 2026-01-23.
- Evidence: OV-SEL-02 fingerprint=b1c55cab148727c9da2556ffe8d8a7cbe0dbd7304c373204cb57e12ca6d580ac and policy sensitivity artifact fingerprint=df99ac9b86229135f2876be1a56d7abf0c730afe714ecee12d86fb9b7b50d871.
- Guardrail: changed_observables=['OV-03x'] (expected ['OV-03x']).

Record (computed)

```json
{
  "active_policy_id": "DQ-01_v2",
  "baseline_policy_id": "DQ-01_v1",
  "date": "2026-01-24",
  "effective_status_date": "2026-01-23",
  "evidence": {
    "evidence_artifact_fingerprint": "df99ac9b86229135f2876be1a56d7abf0c730afe714ecee12d86fb9b7b50d871",
    "evidence_artifact_relpath": "formal/python/artifacts/diagnostics/OV-DQ-01/OV-DQ-01_policy_sensitivity.json",
    "ov_sel_02_lock": "formal/markdown/locks/observables/OV-SEL-02_selection_status_policy_compare.md",
    "ov_sel_02_record_fingerprint": "b1c55cab148727c9da2556ffe8d8a7cbe0dbd7304c373204cb57e12ca6d580ac"
  },
  "fingerprint": "1d286352547eb0d547c85adeaeeceeb4b092ceb73981e9b20ad07825c4bf298e",
  "guardrails": {
    "benchmark_non_participation_guardrails": [
      "OV-SEL-BM-02",
      "OV-SEL-BM-03",
      "OV-SEL-BM-04"
    ],
    "changed_set_ok": true,
    "expected_changed_observables": [
      "OV-03x"
    ],
    "observed_changed_observables": [
      "OV-03x"
    ]
  },
  "narrative": "DQ-01 active policy activation (bookkeeping-only; no physics claim):\n- Active policy: DQ-01_v2 (q_threshold=1.05).\n- Baseline policy remains pinned: DQ-01_v1 (q_threshold=0.9).\n- Effective status date for selection narratives: 2026-01-23.\n- Evidence: OV-SEL-02 fingerprint=b1c55cab148727c9da2556ffe8d8a7cbe0dbd7304c373204cb57e12ca6d580ac and policy sensitivity artifact fingerprint=df99ac9b86229135f2876be1a56d7abf0c730afe714ecee12d86fb9b7b50d871.\n- Guardrail: changed_observables=['OV-03x'] (expected ['OV-03x']).",
  "q_threshold_active": 1.05,
  "q_threshold_baseline": 0.9,
  "schema": "OV-DQ-03_dq01_active_policy_activation/v1",
  "scope": {
    "applies_to": [
      "OV-03x",
      "OV-04x",
      "OV-XD-04",
      "OV-BR-02"
    ],
    "benchmarks_in_scope": false,
    "layer": "selection_decision_layer",
    "notes": "DQ-01 policy affects decisiveness gating only; does not introduce continuity/averaging or benchmark participation."
  }
}
```

Record fingerprint: `1d286352547eb0d547c85adeaeeceeb4b092ceb73981e9b20ad07825c4bf298e`
