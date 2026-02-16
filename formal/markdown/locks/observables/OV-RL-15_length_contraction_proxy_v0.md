# OV-RL-15 - Length Contraction Proxy Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted RL15 report artifacts only
- Expectation-aware pass semantics for positive/negative controls
- No external truth claim

Reproduce (pinned)
- Command: `.\py.ps1 -m formal.python.tools.rl15_length_contraction_proxy_front_door`
- Outputs: `formal/external_evidence/rl15_length_contraction_proxy_domain_01/rl15_reference_report.json`, `formal/external_evidence/rl15_length_contraction_proxy_domain_01/rl15_candidate_report.json`
- Verify: `.\py.ps1 -m pytest formal/python/tests/test_rl15_length_contraction_proxy_v0_lock.py -q`

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-09",
  "domain_id": "DRBR-DOMAIN-RL-15",
  "fingerprint": "7dd319e2d9f1db89f461b9a8298520ebb20fe51dd075a46b2e92606e5f529dd6",
  "inputs": {
    "artifact_dir": "formal/external_evidence/rl15_length_contraction_proxy_domain_01",
    "candidate_artifact": "formal/external_evidence/rl15_length_contraction_proxy_domain_01/rl15_candidate_report.json",
    "reference_artifact": "formal/external_evidence/rl15_length_contraction_proxy_domain_01/rl15_reference_report.json"
  },
  "observable_id": "OV-RL-15",
  "rows": [
    {
      "artifact_id": "RL15_CONTRACTION_positive_control",
      "diagnostics": {
        "candidate_fingerprint": "ad2d6d67feef936fe2ec1b69f1e63d1eecbb6d03d136d6d355fd2319a8538f47",
        "reference_fingerprint": "ad2d6d67feef936fe2ec1b69f1e63d1eecbb6d03d136d6d355fd2319a8538f47"
      },
      "input_data_fingerprint": "ad2d6d67feef936fe2ec1b69f1e63d1eecbb6d03d136d6d355fd2319a8538f47",
      "input_fingerprint": "ad2d6d67feef936fe2ec1b69f1e63d1eecbb6d03d136d6d355fd2319a8538f47",
      "metric_vector": {
        "L": 1.6,
        "L0": 2.0,
        "beta": 0.6,
        "contraction_ratio": 0.8,
        "contraction_residual": 0.0,
        "eps_break": 0.001,
        "eps_contraction": 1e-08,
        "expected_ratio": 0.8,
        "gamma": 1.25
      },
      "passed": true,
      "reason_codes": [
        "rl15_length_contraction_ok"
      ],
      "source": {
        "candidate_config_tag": "rl15_length_contraction_proxy_v0",
        "candidate_regime_tag": "RL15_Length_Contraction_Proxy",
        "candidate_schema": "RL/length_contraction_front_door_report/v1",
        "case_id": "positive_control",
        "case_kind": "positive_control",
        "reference_config_tag": "rl15_length_contraction_proxy_v0",
        "reference_regime_tag": "RL15_Length_Contraction_Proxy",
        "reference_schema": "RL/length_contraction_front_door_report/v1"
      }
    },
    {
      "artifact_id": "RL15_CONTRACTION_negative_control",
      "diagnostics": {
        "candidate_fingerprint": "ad2d6d67feef936fe2ec1b69f1e63d1eecbb6d03d136d6d355fd2319a8538f47",
        "reference_fingerprint": "ad2d6d67feef936fe2ec1b69f1e63d1eecbb6d03d136d6d355fd2319a8538f47"
      },
      "input_data_fingerprint": "ad2d6d67feef936fe2ec1b69f1e63d1eecbb6d03d136d6d355fd2319a8538f47",
      "input_fingerprint": "ad2d6d67feef936fe2ec1b69f1e63d1eecbb6d03d136d6d355fd2319a8538f47",
      "metric_vector": {
        "L": 2.0,
        "L0": 2.0,
        "beta": 0.6,
        "contraction_ratio": 1.0,
        "contraction_residual": 0.19999999999999996,
        "eps_break": 0.001,
        "eps_contraction": 1e-08,
        "expected_ratio": 0.8,
        "gamma": 1.25
      },
      "passed": true,
      "reason_codes": [
        "rl15_length_contraction_break_detected"
      ],
      "source": {
        "candidate_config_tag": "rl15_length_contraction_proxy_v0",
        "candidate_regime_tag": "RL15_Length_Contraction_Proxy",
        "candidate_schema": "RL/length_contraction_front_door_report/v1",
        "case_id": "negative_control",
        "case_kind": "negative_control",
        "reference_config_tag": "rl15_length_contraction_proxy_v0",
        "reference_regime_tag": "RL15_Length_Contraction_Proxy",
        "reference_schema": "RL/length_contraction_front_door_report/v1"
      }
    }
  ],
  "schema": "OV-RL-15_length_contraction_proxy_comparator/v0",
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
        "RL15_CONTRACTION_positive_control",
        "RL15_CONTRACTION_negative_control"
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

Record fingerprint: `7dd319e2d9f1db89f461b9a8298520ebb20fe51dd075a46b2e92606e5f529dd6`
