# OV-RL-04 - Continuity Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted RL04 report artifacts only
- Explicit failure reason taxonomy for grid/continuity residual/determinism
- No external truth claim

Reproduce
- Run: `.\py.ps1 -m formal.python.tools.rl04_continuity_front_door; .\py.ps1 -m pytest formal/python/tests/test_rl04_continuity_v0_lock.py`
- Expected artifacts: `formal/external_evidence/rl04_continuity_domain_01/rl04_reference_report.json`, `formal/external_evidence/rl04_continuity_domain_01/rl04_candidate_report.json`
- Lock fingerprint must match the value below.

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-09",
  "domain_id": "DRBR-DOMAIN-RL-04",
  "fingerprint": "c6699b38b3c110acfe7141cc0882bfa1b8c4544a4bb33066272b612020e29297",
  "inputs": {
    "artifact_dir": "formal/external_evidence/rl04_continuity_domain_01",
    "candidate_artifact": "formal/external_evidence/rl04_continuity_domain_01/rl04_candidate_report.json",
    "reference_artifact": "formal/external_evidence/rl04_continuity_domain_01/rl04_reference_report.json"
  },
  "observable_id": "OV-RL-04",
  "rows": [
    {
      "artifact_id": "RL04_CONTINUITY",
      "diagnostics": {
        "candidate_fingerprint": "8399704ee5cef227195b244ee9935ab95912f79f9cb916313f35f422264295b4",
        "reference_fingerprint": "4fe5eda7bc0f3df6986c3c03ce4bed7c8546fc61b561e1265ee2d629363eec51",
        "t_count_candidate": 32,
        "t_count_reference": 32,
        "t_grid_aligned": true,
        "t_grid_order_candidate": true,
        "t_grid_order_reference": true,
        "x_count_candidate": 128,
        "x_count_reference": 128,
        "x_grid_aligned": true,
        "x_grid_order_candidate": true,
        "x_grid_order_reference": true
      },
      "input_data_fingerprint": "8399704ee5cef227195b244ee9935ab95912f79f9cb916313f35f422264295b4",
      "input_fingerprint": "8399704ee5cef227195b244ee9935ab95912f79f9cb916313f35f422264295b4",
      "metric_vector": {
        "residual_l2_ratio": 0.04997434219418097,
        "residual_linf_abs": 0.049974342110166305
      },
      "passed": false,
      "reason_codes": [
        "FAIL_CONTINUITY_RESIDUAL"
      ],
      "source": {
        "candidate_config_tag": "rl04-cand-pinned",
        "candidate_regime_tag": "rl04-continuity",
        "candidate_schema": "RL/continuity_front_door_report/v1",
        "reference_config_tag": "rl04-ref-pinned",
        "reference_regime_tag": "rl04-continuity",
        "reference_schema": "RL/continuity_front_door_report/v1"
      }
    }
  ],
  "schema": "OV-RL-04_continuity_comparator/v0",
  "scope_limits": [
    "front_door_only",
    "typed_artifacts_only",
    "deterministic_record_only",
    "discriminative_candidate",
    "within_rep_only",
    "no_external_truth_claim"
  ],
  "status": {
    "blocked": false,
    "reasons": []
  },
  "summary": {
    "artifacts": {
      "fail": [
        "RL04_CONTINUITY"
      ],
      "pass": []
    },
    "counts": {
      "fail": 1,
      "pass": 0
    }
  },
  "tolerance_profile": "pinned"
}
```

Record fingerprint: `c6699b38b3c110acfe7141cc0882bfa1b8c4544a4bb33066272b612020e29297`
