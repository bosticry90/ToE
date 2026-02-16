# CT-01 - No Superluminal Propagation Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted CT-01 report artifacts only
- Expectation-aware pass semantics for positive/negative controls
- No external truth claim

Reproduce (pinned)
- Command: `.\py.ps1 -m formal.python.tools.ct01_no_superluminal_propagation_front_door`
- Outputs: `formal/external_evidence/ct01_no_superluminal_propagation_domain_01/ct01_reference_report.json`, `formal/external_evidence/ct01_no_superluminal_propagation_domain_01/ct01_candidate_report.json`
- Verify: `.\py.ps1 -m pytest formal/python/tests/test_ct01_no_superluminal_propagation_v0_lock.py -q`

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-09",
  "domain_id": "CT-DOMAIN-01",
  "fingerprint": "ecfdd221204f09efe15de78aec31494ef80aabc870d76aa4ec3a60aa63218689",
  "inputs": {
    "artifact_dir": "formal/external_evidence/ct01_no_superluminal_propagation_domain_01",
    "candidate_artifact": "formal/external_evidence/ct01_no_superluminal_propagation_domain_01/ct01_candidate_report.json",
    "reference_artifact": "formal/external_evidence/ct01_no_superluminal_propagation_domain_01/ct01_reference_report.json"
  },
  "observable_id": "CT-01",
  "rows": [
    {
      "artifact_id": "CT01_PROPAGATION_positive_control",
      "diagnostics": {
        "candidate_fingerprint": "fdbd883242cc4ed53009bd39ed951032463170b10215a88968772b63bf47fcb8",
        "reference_fingerprint": "fdbd883242cc4ed53009bd39ed951032463170b10215a88968772b63bf47fcb8"
      },
      "input_data_fingerprint": "fdbd883242cc4ed53009bd39ed951032463170b10215a88968772b63bf47fcb8",
      "input_fingerprint": "fdbd883242cc4ed53009bd39ed951032463170b10215a88968772b63bf47fcb8",
      "metric_vector": {
        "c_cone": 1.0,
        "crossed": true,
        "delta_x": 1.0,
        "eps_break": 0.001,
        "eps_ct01": 1e-08,
        "t_cross": 1.0,
        "u_threshold": 0.001,
        "v_emp": 1.0
      },
      "passed": true,
      "reason_codes": [
        "ct01_within_cone"
      ],
      "source": {
        "candidate_config_tag": "ct01_no_superluminal_propagation_v0",
        "candidate_regime_tag": "CT01_No_Superluminal_Propagation",
        "candidate_schema": "CT-01/no_superluminal_propagation_front_door_report/v1",
        "case_id": "positive_control",
        "case_kind": "positive_control",
        "reference_config_tag": "ct01_no_superluminal_propagation_v0",
        "reference_regime_tag": "CT01_No_Superluminal_Propagation",
        "reference_schema": "CT-01/no_superluminal_propagation_front_door_report/v1"
      }
    },
    {
      "artifact_id": "CT01_PROPAGATION_negative_control",
      "diagnostics": {
        "candidate_fingerprint": "fdbd883242cc4ed53009bd39ed951032463170b10215a88968772b63bf47fcb8",
        "reference_fingerprint": "fdbd883242cc4ed53009bd39ed951032463170b10215a88968772b63bf47fcb8"
      },
      "input_data_fingerprint": "fdbd883242cc4ed53009bd39ed951032463170b10215a88968772b63bf47fcb8",
      "input_fingerprint": "fdbd883242cc4ed53009bd39ed951032463170b10215a88968772b63bf47fcb8",
      "metric_vector": {
        "c_cone": 1.0,
        "crossed": true,
        "delta_x": 1.0,
        "eps_break": 0.001,
        "eps_ct01": 1e-08,
        "t_cross": 0.1,
        "u_threshold": 0.001,
        "v_emp": 10.0
      },
      "passed": true,
      "reason_codes": [
        "ct01_superluminal_detected"
      ],
      "source": {
        "candidate_config_tag": "ct01_no_superluminal_propagation_v0",
        "candidate_regime_tag": "CT01_No_Superluminal_Propagation",
        "candidate_schema": "CT-01/no_superluminal_propagation_front_door_report/v1",
        "case_id": "negative_control",
        "case_kind": "negative_control",
        "reference_config_tag": "ct01_no_superluminal_propagation_v0",
        "reference_regime_tag": "CT01_No_Superluminal_Propagation",
        "reference_schema": "CT-01/no_superluminal_propagation_front_door_report/v1"
      }
    }
  ],
  "schema": "CT-01_no_superluminal_propagation_comparator/v0",
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
        "CT01_PROPAGATION_positive_control",
        "CT01_PROPAGATION_negative_control"
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

Record fingerprint: `ecfdd221204f09efe15de78aec31494ef80aabc870d76aa4ec3a60aa63218689`
