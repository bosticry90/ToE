# CT-05 - Rep-Invariant Admissibility Class Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted CT-05 report artifacts only
- Expectation-aware pass semantics for positive/negative controls
- No external truth claim

Reproduce (pinned)
- Command: `.\py.ps1 -m formal.python.tools.ct05_rep_invariant_admissibility_class_front_door`
- Outputs: `formal/external_evidence/ct05_rep_invariant_admissibility_class_domain_01/ct05_reference_report.json`, `formal/external_evidence/ct05_rep_invariant_admissibility_class_domain_01/ct05_candidate_report.json`
- Verify: `.\py.ps1 -m pytest formal/python/tests/test_ct05_rep_invariant_admissibility_class_v0_lock.py -q`

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-09",
  "domain_id": "CT-DOMAIN-05",
  "fingerprint": "1bee0925b3ad7e7c5209cbb442487fb0f1c30d275284f6dbeba564d967645a8d",
  "inputs": {
    "artifact_dir": "formal/external_evidence/ct05_rep_invariant_admissibility_class_domain_01",
    "candidate_artifact": "formal/external_evidence/ct05_rep_invariant_admissibility_class_domain_01/ct05_candidate_report.json",
    "reference_artifact": "formal/external_evidence/ct05_rep_invariant_admissibility_class_domain_01/ct05_reference_report.json"
  },
  "observable_id": "CT-05",
  "rows": [
    {
      "artifact_id": "CT05_REP_INV_POSITIVE",
      "diagnostics": {
        "candidate_fingerprint": "1627f182c1f114c1ad35430a372fc19d4f6b1eb2c39fbbbd7d6bc7daa2db8311",
        "reference_fingerprint": "1627f182c1f114c1ad35430a372fc19d4f6b1eb2c39fbbbd7d6bc7daa2db8311"
      },
      "input_data_fingerprint": "1627f182c1f114c1ad35430a372fc19d4f6b1eb2c39fbbbd7d6bc7daa2db8311",
      "input_fingerprint": "1627f182c1f114c1ad35430a372fc19d4f6b1eb2c39fbbbd7d6bc7daa2db8311",
      "metric_vector": {
        "admissible_ref": true,
        "admissible_rep": true,
        "bound_ok_ref": true,
        "bound_ok_rep": true,
        "bound_residual": 0.0005918495924121875,
        "eps_bound_residual": 0.001,
        "eps_rep_invariant": 1e-10,
        "rep_delta": 0.0
      },
      "passed": true,
      "reason_codes": [
        "ct05_rep_invariant_ok"
      ],
      "source": {
        "candidate_config_tag": "ct05_rep_invariant_admissibility_class_v0",
        "candidate_regime_tag": "CT05_Rep_Invariant_Admissibility_Class",
        "candidate_schema": "CT-05/rep_invariant_admissibility_class_front_door_report/v1",
        "case_id": "POSITIVE",
        "case_kind": "positive_control",
        "reference_config_tag": "ct05_rep_invariant_admissibility_class_v0",
        "reference_regime_tag": "CT05_Rep_Invariant_Admissibility_Class",
        "reference_schema": "CT-05/rep_invariant_admissibility_class_front_door_report/v1"
      }
    },
    {
      "artifact_id": "CT05_REP_INV_NEG_REP_BREAK",
      "diagnostics": {
        "candidate_fingerprint": "1627f182c1f114c1ad35430a372fc19d4f6b1eb2c39fbbbd7d6bc7daa2db8311",
        "reference_fingerprint": "1627f182c1f114c1ad35430a372fc19d4f6b1eb2c39fbbbd7d6bc7daa2db8311"
      },
      "input_data_fingerprint": "1627f182c1f114c1ad35430a372fc19d4f6b1eb2c39fbbbd7d6bc7daa2db8311",
      "input_fingerprint": "1627f182c1f114c1ad35430a372fc19d4f6b1eb2c39fbbbd7d6bc7daa2db8311",
      "metric_vector": {
        "admissible_ref": true,
        "admissible_rep": true,
        "bound_ok_ref": true,
        "bound_ok_rep": true,
        "bound_residual": 0.010591849592412187,
        "eps_bound_residual": 0.001,
        "eps_rep_invariant": 1e-10,
        "rep_delta": 0.01
      },
      "passed": true,
      "reason_codes": [
        "ct05_rep_break_detected"
      ],
      "source": {
        "candidate_config_tag": "ct05_rep_invariant_admissibility_class_v0",
        "candidate_regime_tag": "CT05_Rep_Invariant_Admissibility_Class",
        "candidate_schema": "CT-05/rep_invariant_admissibility_class_front_door_report/v1",
        "case_id": "NEG_REP_BREAK",
        "case_kind": "negative_control_rep_break",
        "reference_config_tag": "ct05_rep_invariant_admissibility_class_v0",
        "reference_regime_tag": "CT05_Rep_Invariant_Admissibility_Class",
        "reference_schema": "CT-05/rep_invariant_admissibility_class_front_door_report/v1"
      }
    },
    {
      "artifact_id": "CT05_REP_INV_NEG_ADMISSIBILITY",
      "diagnostics": {
        "candidate_fingerprint": "1627f182c1f114c1ad35430a372fc19d4f6b1eb2c39fbbbd7d6bc7daa2db8311",
        "reference_fingerprint": "1627f182c1f114c1ad35430a372fc19d4f6b1eb2c39fbbbd7d6bc7daa2db8311"
      },
      "input_data_fingerprint": "1627f182c1f114c1ad35430a372fc19d4f6b1eb2c39fbbbd7d6bc7daa2db8311",
      "input_fingerprint": "1627f182c1f114c1ad35430a372fc19d4f6b1eb2c39fbbbd7d6bc7daa2db8311",
      "metric_vector": {
        "admissible_ref": false,
        "admissible_rep": false,
        "bound_ok_ref": true,
        "bound_ok_rep": true,
        "bound_residual": 0.0005918495924121875,
        "eps_bound_residual": 0.001,
        "eps_rep_invariant": 1e-10,
        "rep_delta": 0.0
      },
      "passed": true,
      "reason_codes": [
        "ct05_admissibility_break_detected"
      ],
      "source": {
        "candidate_config_tag": "ct05_rep_invariant_admissibility_class_v0",
        "candidate_regime_tag": "CT05_Rep_Invariant_Admissibility_Class",
        "candidate_schema": "CT-05/rep_invariant_admissibility_class_front_door_report/v1",
        "case_id": "NEG_ADMISSIBILITY",
        "case_kind": "negative_control_admissibility",
        "reference_config_tag": "ct05_rep_invariant_admissibility_class_v0",
        "reference_regime_tag": "CT05_Rep_Invariant_Admissibility_Class",
        "reference_schema": "CT-05/rep_invariant_admissibility_class_front_door_report/v1"
      }
    }
  ],
  "schema": "CT-05_rep_invariant_admissibility_class_comparator/v0",
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
        "CT05_REP_INV_POSITIVE",
        "CT05_REP_INV_NEG_REP_BREAK",
        "CT05_REP_INV_NEG_ADMISSIBILITY"
      ]
    },
    "counts": {
      "fail": 0,
      "pass": 3
    }
  },
  "tolerance_profile": "pinned"
}
```

Record fingerprint: `1bee0925b3ad7e7c5209cbb442487fb0f1c30d275284f6dbeba564d967645a8d`
