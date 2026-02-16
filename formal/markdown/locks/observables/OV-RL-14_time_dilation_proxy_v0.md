# OV-RL-14 - Time Dilation Proxy Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted RL14 report artifacts only
- Expectation-aware pass semantics for positive/negative controls
- No external truth claim

Reproduce (pinned)
- Command: `.\py.ps1 -m formal.python.tools.rl14_time_dilation_proxy_front_door`
- Outputs: `formal/external_evidence/rl14_time_dilation_proxy_domain_01/rl14_reference_report.json`, `formal/external_evidence/rl14_time_dilation_proxy_domain_01/rl14_candidate_report.json`
- Verify: `.\py.ps1 -m pytest formal/python/tests/test_rl14_time_dilation_proxy_v0_lock.py -q`

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-09",
  "domain_id": "DRBR-DOMAIN-RL-14",
  "fingerprint": "7b1b64d171a36b94196decb3589414a6738b4e4e387b1bcff77d9dbf232d7b0d",
  "inputs": {
    "artifact_dir": "formal/external_evidence/rl14_time_dilation_proxy_domain_01",
    "candidate_artifact": "formal/external_evidence/rl14_time_dilation_proxy_domain_01/rl14_candidate_report.json",
    "reference_artifact": "formal/external_evidence/rl14_time_dilation_proxy_domain_01/rl14_reference_report.json"
  },
  "observable_id": "OV-RL-14",
  "rows": [
    {
      "artifact_id": "RL14_DILATION_positive_control",
      "diagnostics": {
        "candidate_fingerprint": "a08688eae83adde8eb78d2e3c207287a440e490f7f671886021229caf7a46ac8",
        "reference_fingerprint": "a08688eae83adde8eb78d2e3c207287a440e490f7f671886021229caf7a46ac8"
      },
      "input_data_fingerprint": "a08688eae83adde8eb78d2e3c207287a440e490f7f671886021229caf7a46ac8",
      "input_fingerprint": "a08688eae83adde8eb78d2e3c207287a440e490f7f671886021229caf7a46ac8",
      "metric_vector": {
        "beta": 0.6,
        "delta_t": 2.0,
        "delta_tau": 1.6,
        "dilation_ratio": 0.8,
        "dilation_residual": 0.0,
        "eps_break": 0.001,
        "eps_dilation": 1e-08,
        "expected_ratio": 0.8,
        "gamma": 1.25
      },
      "passed": true,
      "reason_codes": [
        "rl14_time_dilation_ok"
      ],
      "source": {
        "candidate_config_tag": "rl14_time_dilation_proxy_v0",
        "candidate_regime_tag": "RL14_Time_Dilation_Proxy",
        "candidate_schema": "RL/time_dilation_front_door_report/v1",
        "case_id": "positive_control",
        "case_kind": "positive_control",
        "reference_config_tag": "rl14_time_dilation_proxy_v0",
        "reference_regime_tag": "RL14_Time_Dilation_Proxy",
        "reference_schema": "RL/time_dilation_front_door_report/v1"
      }
    },
    {
      "artifact_id": "RL14_DILATION_negative_control",
      "diagnostics": {
        "candidate_fingerprint": "a08688eae83adde8eb78d2e3c207287a440e490f7f671886021229caf7a46ac8",
        "reference_fingerprint": "a08688eae83adde8eb78d2e3c207287a440e490f7f671886021229caf7a46ac8"
      },
      "input_data_fingerprint": "a08688eae83adde8eb78d2e3c207287a440e490f7f671886021229caf7a46ac8",
      "input_fingerprint": "a08688eae83adde8eb78d2e3c207287a440e490f7f671886021229caf7a46ac8",
      "metric_vector": {
        "beta": 0.6,
        "delta_t": 2.0,
        "delta_tau": 2.0,
        "dilation_ratio": 1.0,
        "dilation_residual": 0.19999999999999996,
        "eps_break": 0.001,
        "eps_dilation": 1e-08,
        "expected_ratio": 0.8,
        "gamma": 1.25
      },
      "passed": true,
      "reason_codes": [
        "rl14_time_dilation_break_detected"
      ],
      "source": {
        "candidate_config_tag": "rl14_time_dilation_proxy_v0",
        "candidate_regime_tag": "RL14_Time_Dilation_Proxy",
        "candidate_schema": "RL/time_dilation_front_door_report/v1",
        "case_id": "negative_control",
        "case_kind": "negative_control",
        "reference_config_tag": "rl14_time_dilation_proxy_v0",
        "reference_regime_tag": "RL14_Time_Dilation_Proxy",
        "reference_schema": "RL/time_dilation_front_door_report/v1"
      }
    }
  ],
  "schema": "OV-RL-14_time_dilation_proxy_comparator/v0",
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
        "RL14_DILATION_positive_control",
        "RL14_DILATION_negative_control"
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

Record fingerprint: `7b1b64d171a36b94196decb3589414a6738b4e4e387b1bcff77d9dbf232d7b0d`
