# OV-RL-13 - Velocity Addition Group-Law Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted RL13 report artifacts only
- Expectation-aware pass semantics for positive/negative controls
- No external truth claim

Reproduce (pinned)
- Command: `.\py.ps1 -m formal.python.tools.rl13_velocity_addition_group_law_front_door`
- Outputs: `formal/external_evidence/rl13_velocity_addition_group_law_domain_01/rl13_reference_report.json`, `formal/external_evidence/rl13_velocity_addition_group_law_domain_01/rl13_candidate_report.json`
- Verify: `.\py.ps1 -m pytest formal/python/tests/test_rl13_velocity_addition_group_law_v0_lock.py -q`

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-09",
  "domain_id": "DRBR-DOMAIN-RL-13",
  "fingerprint": "04372b07da84e4749ee8a85ec3156f55b210676898de45bdf0d1f49bd1faea2e",
  "inputs": {
    "artifact_dir": "formal/external_evidence/rl13_velocity_addition_group_law_domain_01",
    "candidate_artifact": "formal/external_evidence/rl13_velocity_addition_group_law_domain_01/rl13_candidate_report.json",
    "reference_artifact": "formal/external_evidence/rl13_velocity_addition_group_law_domain_01/rl13_reference_report.json"
  },
  "observable_id": "OV-RL-13",
  "rows": [
    {
      "artifact_id": "RL13_VELOCITY_positive_control",
      "diagnostics": {
        "candidate_fingerprint": "874f61800c32580ae1d54155c974a0d50cc3955d6df3841610a4b5c578900bba",
        "reference_fingerprint": "874f61800c32580ae1d54155c974a0d50cc3955d6df3841610a4b5c578900bba"
      },
      "input_data_fingerprint": "874f61800c32580ae1d54155c974a0d50cc3955d6df3841610a4b5c578900bba",
      "input_fingerprint": "874f61800c32580ae1d54155c974a0d50cc3955d6df3841610a4b5c578900bba",
      "metric_vector": {
        "addition_residual": 0.0,
        "beta_comp": 0.6249999999999999,
        "beta_expected": 0.6249999999999999,
        "beta_u": 0.3,
        "beta_v": 0.4,
        "eps_addition": 1e-08,
        "eps_break": 0.001
      },
      "passed": true,
      "reason_codes": [
        "rl13_velocity_addition_ok"
      ],
      "source": {
        "candidate_config_tag": "rl13_velocity_addition_group_law_v0",
        "candidate_regime_tag": "RL13_Velocity_Addition_Group_Law",
        "candidate_schema": "RL/velocity_addition_front_door_report/v1",
        "case_id": "positive_control",
        "case_kind": "positive_control",
        "reference_config_tag": "rl13_velocity_addition_group_law_v0",
        "reference_regime_tag": "RL13_Velocity_Addition_Group_Law",
        "reference_schema": "RL/velocity_addition_front_door_report/v1"
      }
    },
    {
      "artifact_id": "RL13_VELOCITY_negative_control",
      "diagnostics": {
        "candidate_fingerprint": "874f61800c32580ae1d54155c974a0d50cc3955d6df3841610a4b5c578900bba",
        "reference_fingerprint": "874f61800c32580ae1d54155c974a0d50cc3955d6df3841610a4b5c578900bba"
      },
      "input_data_fingerprint": "874f61800c32580ae1d54155c974a0d50cc3955d6df3841610a4b5c578900bba",
      "input_fingerprint": "874f61800c32580ae1d54155c974a0d50cc3955d6df3841610a4b5c578900bba",
      "metric_vector": {
        "addition_residual": 0.07500000000000007,
        "beta_comp": 0.7,
        "beta_expected": 0.6249999999999999,
        "beta_u": 0.3,
        "beta_v": 0.4,
        "eps_addition": 1e-08,
        "eps_break": 0.001
      },
      "passed": true,
      "reason_codes": [
        "rl13_addition_break_detected"
      ],
      "source": {
        "candidate_config_tag": "rl13_velocity_addition_group_law_v0",
        "candidate_regime_tag": "RL13_Velocity_Addition_Group_Law",
        "candidate_schema": "RL/velocity_addition_front_door_report/v1",
        "case_id": "negative_control",
        "case_kind": "negative_control",
        "reference_config_tag": "rl13_velocity_addition_group_law_v0",
        "reference_regime_tag": "RL13_Velocity_Addition_Group_Law",
        "reference_schema": "RL/velocity_addition_front_door_report/v1"
      }
    }
  ],
  "schema": "OV-RL-13_velocity_addition_group_law_comparator/v0",
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
        "RL13_VELOCITY_positive_control",
        "RL13_VELOCITY_negative_control"
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

Record fingerprint: `04372b07da84e4749ee8a85ec3156f55b210676898de45bdf0d1f49bd1faea2e`
