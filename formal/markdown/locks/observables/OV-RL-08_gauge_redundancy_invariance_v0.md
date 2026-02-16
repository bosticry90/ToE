# OV-RL-08 - Gauge Redundancy Invariance Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted RL08 report artifacts only
- Expectation-aware pass semantics for positive/negative controls
- No external truth claim

Reproduce (pinned)
- Command: `.\py.ps1 -m formal.python.tools.rl08_gauge_redundancy_invariance_front_door`
- Outputs: `formal/external_evidence/rl08_gauge_redundancy_invariance_domain_01/rl08_reference_report.json`, `formal/external_evidence/rl08_gauge_redundancy_invariance_domain_01/rl08_candidate_report.json`
- Verify: `.\py.ps1 -m pytest formal/python/tests/test_rl08_gauge_redundancy_invariance_v0_lock.py -q`

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-09",
  "domain_id": "DRBR-DOMAIN-RL-08",
  "fingerprint": "8a17fedc29200699f5c24af3d5139699a437554cbe5d4ccc8bd0020949e3e31f",
  "inputs": {
    "artifact_dir": "formal/external_evidence/rl08_gauge_redundancy_invariance_domain_01",
    "candidate_artifact": "formal/external_evidence/rl08_gauge_redundancy_invariance_domain_01/rl08_candidate_report.json",
    "reference_artifact": "formal/external_evidence/rl08_gauge_redundancy_invariance_domain_01/rl08_reference_report.json"
  },
  "observable_id": "OV-RL-08",
  "rows": [
    {
      "artifact_id": "RL08_GAUGE_POSITIVE",
      "diagnostics": {
        "candidate_fingerprint": "a7ffa82e89319ad3820494b23d1901137d1757ac398c3252a0e568387c5727fc",
        "reference_fingerprint": "f1b06dd9a6efea678823f702bb8503d92fc8f783b5dbff36c9e962b67d2df52b",
        "x_count_candidate": 128,
        "x_count_reference": 128,
        "x_grid_aligned": true,
        "x_grid_order_candidate": true,
        "x_grid_order_reference": true
      },
      "input_data_fingerprint": "a7ffa82e89319ad3820494b23d1901137d1757ac398c3252a0e568387c5727fc",
      "input_fingerprint": "a7ffa82e89319ad3820494b23d1901137d1757ac398c3252a0e568387c5727fc",
      "metric_vector": {
        "eps_break": 0.001,
        "eps_invariant": 1e-10,
        "residual_maxabs": 1.1102230246251565e-15
      },
      "passed": true,
      "reason_codes": [
        "rl08_gauge_invariance_ok"
      ],
      "source": {
        "candidate_config_tag": "rl08-cand-pinned",
        "candidate_regime_tag": "rl08-gauge-redundancy",
        "candidate_schema": "RL/gauge_redundancy_front_door_report/v1",
        "case_id": "POSITIVE",
        "case_kind": "positive_control",
        "reference_config_tag": "rl08-ref-pinned",
        "reference_regime_tag": "rl08-gauge-redundancy",
        "reference_schema": "RL/gauge_redundancy_front_door_report/v1"
      }
    },
    {
      "artifact_id": "RL08_GAUGE_NEGATIVE",
      "diagnostics": {
        "candidate_fingerprint": "a7ffa82e89319ad3820494b23d1901137d1757ac398c3252a0e568387c5727fc",
        "reference_fingerprint": "f1b06dd9a6efea678823f702bb8503d92fc8f783b5dbff36c9e962b67d2df52b",
        "x_count_candidate": 128,
        "x_count_reference": 128,
        "x_grid_aligned": true,
        "x_grid_order_candidate": true,
        "x_grid_order_reference": true
      },
      "input_data_fingerprint": "a7ffa82e89319ad3820494b23d1901137d1757ac398c3252a0e568387c5727fc",
      "input_fingerprint": "a7ffa82e89319ad3820494b23d1901137d1757ac398c3252a0e568387c5727fc",
      "metric_vector": {
        "eps_break": 0.001,
        "eps_invariant": 1e-10,
        "residual_maxabs": 0.08320969719284599
      },
      "passed": true,
      "reason_codes": [
        "rl08_gauge_break_detected"
      ],
      "source": {
        "candidate_config_tag": "rl08-cand-pinned",
        "candidate_regime_tag": "rl08-gauge-redundancy",
        "candidate_schema": "RL/gauge_redundancy_front_door_report/v1",
        "case_id": "NEGATIVE",
        "case_kind": "negative_control",
        "reference_config_tag": "rl08-ref-pinned",
        "reference_regime_tag": "rl08-gauge-redundancy",
        "reference_schema": "RL/gauge_redundancy_front_door_report/v1"
      }
    }
  ],
  "schema": "OV-RL-08_gauge_redundancy_invariance_comparator/v0",
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
      "fail": [],
      "pass": [
        "RL08_GAUGE_POSITIVE",
        "RL08_GAUGE_NEGATIVE"
      ]
    },
    "counts": {
      "fail": 0,
      "pass": 2
    }
  },
  "tolerance_profile": "pinned"
}
```

Record fingerprint: `8a17fedc29200699f5c24af3d5139699a437554cbe5d4ccc8bd0020949e3e31f`
