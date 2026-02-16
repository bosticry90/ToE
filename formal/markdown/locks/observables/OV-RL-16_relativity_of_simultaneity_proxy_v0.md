# OV-RL-16 - Relativity of Simultaneity Proxy Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted RL16 report artifacts only
- Expectation-aware pass semantics for positive/negative controls
- No external truth claim

Reproduce (pinned)
- Command: `.\py.ps1 -m formal.python.tools.rl16_relativity_of_simultaneity_proxy_front_door`
- Outputs: `formal/external_evidence/rl16_relativity_of_simultaneity_proxy_domain_01/rl16_reference_report.json`, `formal/external_evidence/rl16_relativity_of_simultaneity_proxy_domain_01/rl16_candidate_report.json`
- Verify: `.\py.ps1 -m pytest formal/python/tests/test_rl16_relativity_of_simultaneity_proxy_v0_lock.py -q`

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-09",
  "domain_id": "DRBR-DOMAIN-RL-16",
  "fingerprint": "511d03b63d5c117a135cbf8548af1763eac747d2187bf4856b43efda9fff371e",
  "inputs": {
    "artifact_dir": "formal/external_evidence/rl16_relativity_of_simultaneity_proxy_domain_01",
    "candidate_artifact": "formal/external_evidence/rl16_relativity_of_simultaneity_proxy_domain_01/rl16_candidate_report.json",
    "reference_artifact": "formal/external_evidence/rl16_relativity_of_simultaneity_proxy_domain_01/rl16_reference_report.json"
  },
  "observable_id": "OV-RL-16",
  "rows": [
    {
      "artifact_id": "RL16_SIMULTANEITY_positive_control",
      "diagnostics": {
        "candidate_fingerprint": "5df02b85708c2a8dff9299100cfec79b62aaa44e548f1906de8d1a40b77dd2c8",
        "reference_fingerprint": "5df02b85708c2a8dff9299100cfec79b62aaa44e548f1906de8d1a40b77dd2c8"
      },
      "input_data_fingerprint": "5df02b85708c2a8dff9299100cfec79b62aaa44e548f1906de8d1a40b77dd2c8",
      "input_fingerprint": "5df02b85708c2a8dff9299100cfec79b62aaa44e548f1906de8d1a40b77dd2c8",
      "metric_vector": {
        "beta": 0.6,
        "delta_t": 0.2,
        "delta_t_prime": -0.875,
        "delta_x": 1.5,
        "eps_break": 0.001,
        "eps_simultaneity": 1e-08,
        "expected_delta_t_prime": -0.875,
        "gamma": 1.25,
        "simultaneity_residual": 0.0
      },
      "passed": true,
      "reason_codes": [
        "rl16_simultaneity_ok"
      ],
      "source": {
        "candidate_config_tag": "rl16_relativity_of_simultaneity_proxy_v0",
        "candidate_regime_tag": "RL16_Relativity_Of_Simultaneity_Proxy",
        "candidate_schema": "RL/relativity_of_simultaneity_front_door_report/v1",
        "case_id": "positive_control",
        "case_kind": "positive_control",
        "reference_config_tag": "rl16_relativity_of_simultaneity_proxy_v0",
        "reference_regime_tag": "RL16_Relativity_Of_Simultaneity_Proxy",
        "reference_schema": "RL/relativity_of_simultaneity_front_door_report/v1"
      }
    },
    {
      "artifact_id": "RL16_SIMULTANEITY_negative_control",
      "diagnostics": {
        "candidate_fingerprint": "5df02b85708c2a8dff9299100cfec79b62aaa44e548f1906de8d1a40b77dd2c8",
        "reference_fingerprint": "5df02b85708c2a8dff9299100cfec79b62aaa44e548f1906de8d1a40b77dd2c8"
      },
      "input_data_fingerprint": "5df02b85708c2a8dff9299100cfec79b62aaa44e548f1906de8d1a40b77dd2c8",
      "input_fingerprint": "5df02b85708c2a8dff9299100cfec79b62aaa44e548f1906de8d1a40b77dd2c8",
      "metric_vector": {
        "beta": 0.6,
        "delta_t": 0.2,
        "delta_t_prime": 0.2,
        "delta_x": 1.5,
        "eps_break": 0.001,
        "eps_simultaneity": 1e-08,
        "expected_delta_t_prime": -0.875,
        "gamma": 1.25,
        "simultaneity_residual": 1.075
      },
      "passed": true,
      "reason_codes": [
        "rl16_simultaneity_break_detected"
      ],
      "source": {
        "candidate_config_tag": "rl16_relativity_of_simultaneity_proxy_v0",
        "candidate_regime_tag": "RL16_Relativity_Of_Simultaneity_Proxy",
        "candidate_schema": "RL/relativity_of_simultaneity_front_door_report/v1",
        "case_id": "negative_control",
        "case_kind": "negative_control",
        "reference_config_tag": "rl16_relativity_of_simultaneity_proxy_v0",
        "reference_regime_tag": "RL16_Relativity_Of_Simultaneity_Proxy",
        "reference_schema": "RL/relativity_of_simultaneity_front_door_report/v1"
      }
    }
  ],
  "schema": "OV-RL-16_relativity_of_simultaneity_proxy_comparator/v0",
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
        "RL16_SIMULTANEITY_positive_control",
        "RL16_SIMULTANEITY_negative_control"
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

Record fingerprint: `511d03b63d5c117a135cbf8548af1763eac747d2187bf4856b43efda9fff371e`
