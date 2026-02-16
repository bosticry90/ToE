# OV-RL-03 - Weak-Field Poisson Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted RL03 report artifacts only
- Explicit failure reason taxonomy for grid/Poisson residual/determinism
- No external truth claim

Reproduce
- Run: `.\py.ps1 -m formal.python.tools.rl03_weak_field_poisson_front_door; .\py.ps1 -m pytest formal/python/tests/test_rl03_weak_field_poisson_v0_lock.py`
- Expected artifacts: `formal/external_evidence/rl03_weak_field_poisson_domain_01/rl03_reference_report.json`, `formal/external_evidence/rl03_weak_field_poisson_domain_01/rl03_candidate_report.json`
- Lock fingerprint must match the value below.

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-09",
  "domain_id": "DRBR-DOMAIN-RL-03",
  "fingerprint": "a14ccc73f08def08864b1d9950e505d381efa40272f088e3fd5df81ea9e52311",
  "inputs": {
    "artifact_dir": "formal/external_evidence/rl03_weak_field_poisson_domain_01",
    "candidate_artifact": "formal/external_evidence/rl03_weak_field_poisson_domain_01/rl03_candidate_report.json",
    "reference_artifact": "formal/external_evidence/rl03_weak_field_poisson_domain_01/rl03_reference_report.json"
  },
  "observable_id": "OV-RL-03",
  "rows": [
    {
      "artifact_id": "RL03_WEAK_FIELD_POISSON",
      "diagnostics": {
        "candidate_fingerprint": "65de90d87425ed0024a8018c3a0b9d1b98be5004c8570f5f2cbd2a2f6a11922a",
        "gauge_mean": 4.336808689942018e-19,
        "reference_fingerprint": "b2c1054fff581b87cc55b9a116054785a6675257cda9abc04e92a8dfd62c96f9",
        "x_count_candidate": 128,
        "x_count_reference": 128,
        "x_grid_aligned": true,
        "x_grid_order_candidate": true,
        "x_grid_order_reference": true
      },
      "input_data_fingerprint": "65de90d87425ed0024a8018c3a0b9d1b98be5004c8570f5f2cbd2a2f6a11922a",
      "input_fingerprint": "65de90d87425ed0024a8018c3a0b9d1b98be5004c8570f5f2cbd2a2f6a11922a",
      "metric_vector": {
        "residual_l2_ratio": 0.595391091803968,
        "residual_linf_abs": 0.2511709978608979
      },
      "passed": false,
      "reason_codes": [
        "FAIL_POISSON_RESIDUAL"
      ],
      "source": {
        "candidate_config_tag": "rl03-cand-pinned",
        "candidate_regime_tag": "rl03-weak-field",
        "candidate_schema": "RL/weak_field_poisson_front_door_report/v1",
        "reference_config_tag": "rl03-ref-pinned",
        "reference_regime_tag": "rl03-weak-field",
        "reference_schema": "RL/weak_field_poisson_front_door_report/v1"
      }
    }
  ],
  "schema": "OV-RL-03_weak_field_poisson_comparator/v0",
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
        "RL03_WEAK_FIELD_POISSON"
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

Record fingerprint: `a14ccc73f08def08864b1d9950e505d381efa40272f088e3fd5df81ea9e52311`
