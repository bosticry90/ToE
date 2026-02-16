# CT-04 - Minimality No-Go Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted CT-04 report artifacts only
- Expectation-aware pass semantics for positive/negative controls
- No external truth claim

Reproduce (pinned)
- Command: `.\py.ps1 -m formal.python.tools.ct04_minimality_no_go_front_door`
- Outputs: `formal/external_evidence/ct04_minimality_no_go_domain_01/ct04_reference_report.json`, `formal/external_evidence/ct04_minimality_no_go_domain_01/ct04_candidate_report.json`
- Verify: `.\py.ps1 -m pytest formal/python/tests/test_ct04_minimality_no_go_v0_lock.py -q`

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-09",
  "domain_id": "CT-DOMAIN-04",
  "fingerprint": "5c491a0184cb300bb960f4e60530aabb28099e9dab769e25ed33b7e9aac7f1d3",
  "inputs": {
    "artifact_dir": "formal/external_evidence/ct04_minimality_no_go_domain_01",
    "candidate_artifact": "formal/external_evidence/ct04_minimality_no_go_domain_01/ct04_candidate_report.json",
    "reference_artifact": "formal/external_evidence/ct04_minimality_no_go_domain_01/ct04_reference_report.json"
  },
  "observable_id": "CT-04",
  "rows": [
    {
      "artifact_id": "CT04_MINIMALITY_POSITIVE",
      "diagnostics": {
        "candidate_fingerprint": "d46a2ebab12f209e75807a137a01a87afe09004cca02d6b3d4308cf6b09a1a91",
        "reference_fingerprint": "d46a2ebab12f209e75807a137a01a87afe09004cca02d6b3d4308cf6b09a1a91"
      },
      "input_data_fingerprint": "d46a2ebab12f209e75807a137a01a87afe09004cca02d6b3d4308cf6b09a1a91",
      "input_fingerprint": "d46a2ebab12f209e75807a137a01a87afe09004cca02d6b3d4308cf6b09a1a91",
      "metric_vector": {
        "cfl": 0.1,
        "cfl_max": 1.0,
        "constraint_mode": "cfl_bound",
        "dt": 0.004908738521234052,
        "eps_break": 0.001,
        "eps_drift": 0.005,
        "max_rel_drift": 0.0005966084844298418,
        "rel_drift": 8.696004559631644e-05,
        "steps": 2000
      },
      "passed": true,
      "reason_codes": [
        "ct04_minimality_ok"
      ],
      "source": {
        "candidate_config_tag": "ct04_minimality_no_go_v0",
        "candidate_regime_tag": "CT04_Minimality_No_Go",
        "candidate_schema": "CT-04/minimality_no_go_front_door_report/v1",
        "case_id": "POSITIVE",
        "case_kind": "positive_control",
        "reference_config_tag": "ct04_minimality_no_go_v0",
        "reference_regime_tag": "CT04_Minimality_No_Go",
        "reference_schema": "CT-04/minimality_no_go_front_door_report/v1"
      }
    },
    {
      "artifact_id": "CT04_MINIMALITY_NEGATIVE",
      "diagnostics": {
        "candidate_fingerprint": "d46a2ebab12f209e75807a137a01a87afe09004cca02d6b3d4308cf6b09a1a91",
        "reference_fingerprint": "d46a2ebab12f209e75807a137a01a87afe09004cca02d6b3d4308cf6b09a1a91"
      },
      "input_data_fingerprint": "d46a2ebab12f209e75807a137a01a87afe09004cca02d6b3d4308cf6b09a1a91",
      "input_fingerprint": "d46a2ebab12f209e75807a137a01a87afe09004cca02d6b3d4308cf6b09a1a91",
      "metric_vector": {
        "cfl": 1.05,
        "cfl_max": 1.0,
        "constraint_mode": "cfl_removed",
        "dt": 0.05154175447295754,
        "eps_break": 0.001,
        "eps_drift": 0.005,
        "max_rel_drift": 4.544471913419606e-05,
        "rel_drift": 4.544471913419606e-05,
        "steps": 20
      },
      "passed": true,
      "reason_codes": [
        "ct04_minimality_violation_detected"
      ],
      "source": {
        "candidate_config_tag": "ct04_minimality_no_go_v0",
        "candidate_regime_tag": "CT04_Minimality_No_Go",
        "candidate_schema": "CT-04/minimality_no_go_front_door_report/v1",
        "case_id": "NEGATIVE",
        "case_kind": "negative_control",
        "reference_config_tag": "ct04_minimality_no_go_v0",
        "reference_regime_tag": "CT04_Minimality_No_Go",
        "reference_schema": "CT-04/minimality_no_go_front_door_report/v1"
      }
    }
  ],
  "schema": "CT-04_minimality_no_go_comparator/v0",
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
        "CT04_MINIMALITY_POSITIVE",
        "CT04_MINIMALITY_NEGATIVE"
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

Record fingerprint: `5c491a0184cb300bb960f4e60530aabb28099e9dab769e25ed33b7e9aac7f1d3`
