# CX-01 - Update Contractivity Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted CX-01 report artifacts only
- Expectation-aware pass semantics for positive/negative controls
- Admissibility predicate only (within-rep)
- No external truth claim

Reproduce (pinned)
- Command: `.\py.ps1 -m formal.python.tools.cx01_update_contractivity_front_door`
- Outputs: `formal/external_evidence/cx01_update_contractivity_domain_01/cx01_reference_report.json`, `formal/external_evidence/cx01_update_contractivity_domain_01/cx01_candidate_report.json`
- Verify: `.\py.ps1 -m pytest formal/python/tests/test_cx01_update_contractivity_v0_lock.py -q`

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-11",
  "domain_id": "CX-DOMAIN-01",
  "fingerprint": "54e76e49360e16c49f545b31778c39ffbc544cacc27c2de1289873fab293ba81",
  "inputs": {
    "artifact_dir": "formal/external_evidence/cx01_update_contractivity_domain_01",
    "candidate_artifact": "formal/external_evidence/cx01_update_contractivity_domain_01/cx01_candidate_report.json",
    "reference_artifact": "formal/external_evidence/cx01_update_contractivity_domain_01/cx01_reference_report.json"
  },
  "observable_id": "CX-01",
  "rows": [
    {
      "artifact_id": "CX01_CONTRACTIVITY_POSITIVE",
      "diagnostics": {
        "candidate_fingerprint": "a6c54c8462cc2859fde4d9ff019313e6a17aa2117273a5f437009f0bc1b62416",
        "reference_fingerprint": "a6c54c8462cc2859fde4d9ff019313e6a17aa2117273a5f437009f0bc1b62416"
      },
      "input_data_fingerprint": "a6c54c8462cc2859fde4d9ff019313e6a17aa2117273a5f437009f0bc1b62416",
      "input_fingerprint": "a6c54c8462cc2859fde4d9ff019313e6a17aa2117273a5f437009f0bc1b62416",
      "metric_vector": {
        "admissibility_bound": 1.0,
        "contraction_factor_per_step": 0.8,
        "distance_in": 1.4402735527588588,
        "distance_out": 0.7374200590125358,
        "empirical_lipschitz": 0.5120000000000001,
        "eps_break": 0.001,
        "eps_contractivity": 1e-08,
        "expected_empirical_lipschitz": 0.5120000000000001,
        "steps": 3,
        "update_mode": "linear_scale_contractive"
      },
      "passed": true,
      "reason_codes": [
        "cx01_contractive_update_ok"
      ],
      "source": {
        "candidate_config_tag": "cx01_update_contractivity_v0",
        "candidate_regime_tag": "CX01_Update_Contractivity",
        "candidate_schema": "CX-01/update_contractivity_front_door_report/v1",
        "case_id": "POSITIVE",
        "case_kind": "positive_control",
        "reference_config_tag": "cx01_update_contractivity_v0",
        "reference_regime_tag": "CX01_Update_Contractivity",
        "reference_schema": "CX-01/update_contractivity_front_door_report/v1"
      }
    },
    {
      "artifact_id": "CX01_CONTRACTIVITY_NEGATIVE",
      "diagnostics": {
        "candidate_fingerprint": "a6c54c8462cc2859fde4d9ff019313e6a17aa2117273a5f437009f0bc1b62416",
        "reference_fingerprint": "a6c54c8462cc2859fde4d9ff019313e6a17aa2117273a5f437009f0bc1b62416"
      },
      "input_data_fingerprint": "a6c54c8462cc2859fde4d9ff019313e6a17aa2117273a5f437009f0bc1b62416",
      "input_fingerprint": "a6c54c8462cc2859fde4d9ff019313e6a17aa2117273a5f437009f0bc1b62416",
      "metric_vector": {
        "admissibility_bound": 1.0,
        "contraction_factor_per_step": 1.05,
        "distance_in": 1.4402735527588588,
        "distance_out": 1.667296671512474,
        "empirical_lipschitz": 1.157625,
        "eps_break": 0.001,
        "eps_contractivity": 1e-08,
        "expected_empirical_lipschitz": 1.1576250000000001,
        "steps": 3,
        "update_mode": "linear_scale_break"
      },
      "passed": true,
      "reason_codes": [
        "cx01_contractivity_break_detected"
      ],
      "source": {
        "candidate_config_tag": "cx01_update_contractivity_v0",
        "candidate_regime_tag": "CX01_Update_Contractivity",
        "candidate_schema": "CX-01/update_contractivity_front_door_report/v1",
        "case_id": "NEGATIVE",
        "case_kind": "negative_control",
        "reference_config_tag": "cx01_update_contractivity_v0",
        "reference_regime_tag": "CX01_Update_Contractivity",
        "reference_schema": "CX-01/update_contractivity_front_door_report/v1"
      }
    }
  ],
  "schema": "CX-01_update_contractivity_comparator/v0",
  "scope_limits": [
    "front_door_only",
    "typed_artifacts_only",
    "deterministic_record_only",
    "discriminative_candidate",
    "within_rep_only",
    "admissibility_predicate_only",
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
        "CX01_CONTRACTIVITY_POSITIVE",
        "CX01_CONTRACTIVITY_NEGATIVE"
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

Record fingerprint: `54e76e49360e16c49f545b31778c39ffbc544cacc27c2de1289873fab293ba81`
