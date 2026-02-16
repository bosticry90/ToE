# CT-02 - Energy/Causality Update Bounds Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted CT-02 report artifacts only
- Expectation-aware pass semantics for positive/negative controls
- No external truth claim

Reproduce (pinned)
- Command: `.\py.ps1 -m formal.python.tools.ct02_energy_causality_update_bounds_front_door`
- Outputs: `formal/external_evidence/ct02_energy_causality_update_bounds_domain_01/ct02_reference_report.json`, `formal/external_evidence/ct02_energy_causality_update_bounds_domain_01/ct02_candidate_report.json`
- Verify: `.\py.ps1 -m pytest formal/python/tests/test_ct02_energy_causality_update_bounds_v0_lock.py -q`

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-09",
  "domain_id": "CT-DOMAIN-02",
  "fingerprint": "78746e20b6d17acbb5ea1507173aa2ec8e9586b3263f08e450994c45e8883108",
  "inputs": {
    "artifact_dir": "formal/external_evidence/ct02_energy_causality_update_bounds_domain_01",
    "candidate_artifact": "formal/external_evidence/ct02_energy_causality_update_bounds_domain_01/ct02_candidate_report.json",
    "reference_artifact": "formal/external_evidence/ct02_energy_causality_update_bounds_domain_01/ct02_reference_report.json"
  },
  "observable_id": "CT-02",
  "rows": [
    {
      "artifact_id": "CT02_UPDATE_POSITIVE",
      "diagnostics": {
        "candidate_fingerprint": "cce0c8ba63c53901bc68ea94e7c98b0d2ab29da4b2f53962221823392422e122",
        "reference_fingerprint": "cce0c8ba63c53901bc68ea94e7c98b0d2ab29da4b2f53962221823392422e122"
      },
      "input_data_fingerprint": "cce0c8ba63c53901bc68ea94e7c98b0d2ab29da4b2f53962221823392422e122",
      "input_fingerprint": "cce0c8ba63c53901bc68ea94e7c98b0d2ab29da4b2f53962221823392422e122",
      "metric_vector": {
        "cfl": 0.1,
        "cfl_max": 1.0,
        "dt": 0.004908738521234052,
        "eps_break": 0.001,
        "eps_drift": 0.005,
        "eps_drop": 0.1,
        "gamma": 0.0,
        "max_rel_drift": 0.0005966084844298418,
        "rel_drift": 8.696004559631644e-05,
        "rel_drop": -8.696004559631644e-05,
        "steps": 2000
      },
      "passed": true,
      "reason_codes": [
        "ct02_energy_causality_ok"
      ],
      "source": {
        "candidate_config_tag": "ct02_energy_causality_update_bounds_v0",
        "candidate_regime_tag": "CT02_Energy_Causality_Update_Bounds",
        "candidate_schema": "CT-02/energy_causality_update_bounds_front_door_report/v1",
        "case_id": "POSITIVE",
        "case_kind": "positive_control",
        "reference_config_tag": "ct02_energy_causality_update_bounds_v0",
        "reference_regime_tag": "CT02_Energy_Causality_Update_Bounds",
        "reference_schema": "CT-02/energy_causality_update_bounds_front_door_report/v1"
      }
    },
    {
      "artifact_id": "CT02_UPDATE_NEGATIVE",
      "diagnostics": {
        "candidate_fingerprint": "cce0c8ba63c53901bc68ea94e7c98b0d2ab29da4b2f53962221823392422e122",
        "reference_fingerprint": "cce0c8ba63c53901bc68ea94e7c98b0d2ab29da4b2f53962221823392422e122"
      },
      "input_data_fingerprint": "cce0c8ba63c53901bc68ea94e7c98b0d2ab29da4b2f53962221823392422e122",
      "input_fingerprint": "cce0c8ba63c53901bc68ea94e7c98b0d2ab29da4b2f53962221823392422e122",
      "metric_vector": {
        "cfl": 1.05,
        "cfl_max": 1.0,
        "dt": 0.05154175447295754,
        "eps_break": 0.001,
        "eps_drift": 0.005,
        "eps_drop": 0.1,
        "gamma": 0.05,
        "max_rel_drift": 0.14030974925618445,
        "rel_drift": 0.14030974925618445,
        "rel_drop": 0.14030974925618445,
        "steps": 50
      },
      "passed": true,
      "reason_codes": [
        "ct02_energy_causality_break_detected"
      ],
      "source": {
        "candidate_config_tag": "ct02_energy_causality_update_bounds_v0",
        "candidate_regime_tag": "CT02_Energy_Causality_Update_Bounds",
        "candidate_schema": "CT-02/energy_causality_update_bounds_front_door_report/v1",
        "case_id": "NEGATIVE",
        "case_kind": "negative_control",
        "reference_config_tag": "ct02_energy_causality_update_bounds_v0",
        "reference_regime_tag": "CT02_Energy_Causality_Update_Bounds",
        "reference_schema": "CT-02/energy_causality_update_bounds_front_door_report/v1"
      }
    }
  ],
  "schema": "CT-02_energy_causality_update_bounds_comparator/v0",
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
        "CT02_UPDATE_POSITIVE",
        "CT02_UPDATE_NEGATIVE"
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

Record fingerprint: `78746e20b6d17acbb5ea1507173aa2ec8e9586b3263f08e450994c45e8883108`
