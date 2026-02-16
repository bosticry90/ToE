# CT-03 - Energy/Causality Rep-Variant Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted CT-03 report artifacts only
- Expectation-aware pass semantics for positive/negative controls
- No external truth claim

Reproduce (pinned)
- Command: `.\py.ps1 -m formal.python.tools.ct03_energy_causality_rep_variant_front_door`
- Outputs: `formal/external_evidence/ct03_energy_causality_rep_variant_domain_01/ct03_reference_report.json`, `formal/external_evidence/ct03_energy_causality_rep_variant_domain_01/ct03_candidate_report.json`
- Verify: `.\py.ps1 -m pytest formal/python/tests/test_ct03_energy_causality_rep_variant_v0_lock.py -q`

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-09",
  "domain_id": "CT-DOMAIN-03",
  "fingerprint": "2936b26f10c5d755c6e08f4a86dd9e4b6182cc00f83e63677592d421fe352ab6",
  "inputs": {
    "artifact_dir": "formal/external_evidence/ct03_energy_causality_rep_variant_domain_01",
    "candidate_artifact": "formal/external_evidence/ct03_energy_causality_rep_variant_domain_01/ct03_candidate_report.json",
    "reference_artifact": "formal/external_evidence/ct03_energy_causality_rep_variant_domain_01/ct03_reference_report.json"
  },
  "observable_id": "CT-03",
  "rows": [
    {
      "artifact_id": "CT03_UPDATE_POSITIVE",
      "diagnostics": {
        "candidate_fingerprint": "fb5ea8570f7698876619f68e73911d2a8df2a0c3704e4017b3a1d65cb9925eec",
        "reference_fingerprint": "fb5ea8570f7698876619f68e73911d2a8df2a0c3704e4017b3a1d65cb9925eec"
      },
      "input_data_fingerprint": "fb5ea8570f7698876619f68e73911d2a8df2a0c3704e4017b3a1d65cb9925eec",
      "input_fingerprint": "fb5ea8570f7698876619f68e73911d2a8df2a0c3704e4017b3a1d65cb9925eec",
      "metric_vector": {
        "cfl": 0.1,
        "cfl_max": 1.0,
        "dt": 0.004363323129985824,
        "eps_break": 0.001,
        "eps_drift": 0.005,
        "eps_drop": 0.1,
        "gamma": 0.0,
        "max_rel_drift": 4.7588920176543055e-06,
        "rel_drift": 1.969471803103946e-06,
        "rel_drop": 1.969471803103946e-06,
        "steps": 2000
      },
      "passed": true,
      "reason_codes": [
        "ct03_energy_causality_ok"
      ],
      "source": {
        "candidate_config_tag": "ct03_energy_causality_rep_variant_v0",
        "candidate_regime_tag": "CT03_Energy_Causality_Rep_Variant",
        "candidate_schema": "CT-03/energy_causality_rep_variant_front_door_report/v1",
        "case_id": "POSITIVE",
        "case_kind": "positive_control",
        "reference_config_tag": "ct03_energy_causality_rep_variant_v0",
        "reference_regime_tag": "CT03_Energy_Causality_Rep_Variant",
        "reference_schema": "CT-03/energy_causality_rep_variant_front_door_report/v1"
      }
    },
    {
      "artifact_id": "CT03_UPDATE_NEGATIVE",
      "diagnostics": {
        "candidate_fingerprint": "fb5ea8570f7698876619f68e73911d2a8df2a0c3704e4017b3a1d65cb9925eec",
        "reference_fingerprint": "fb5ea8570f7698876619f68e73911d2a8df2a0c3704e4017b3a1d65cb9925eec"
      },
      "input_data_fingerprint": "fb5ea8570f7698876619f68e73911d2a8df2a0c3704e4017b3a1d65cb9925eec",
      "input_fingerprint": "fb5ea8570f7698876619f68e73911d2a8df2a0c3704e4017b3a1d65cb9925eec",
      "metric_vector": {
        "cfl": 1.05,
        "cfl_max": 1.0,
        "dt": 0.04581489286485115,
        "eps_break": 0.001,
        "eps_drift": 0.005,
        "eps_drop": 0.1,
        "gamma": 0.05,
        "max_rel_drift": 0.1293981025596069,
        "rel_drift": 0.1293981025596069,
        "rel_drop": 0.1293981025596069,
        "steps": 50
      },
      "passed": true,
      "reason_codes": [
        "ct03_energy_causality_break_detected"
      ],
      "source": {
        "candidate_config_tag": "ct03_energy_causality_rep_variant_v0",
        "candidate_regime_tag": "CT03_Energy_Causality_Rep_Variant",
        "candidate_schema": "CT-03/energy_causality_rep_variant_front_door_report/v1",
        "case_id": "NEGATIVE",
        "case_kind": "negative_control",
        "reference_config_tag": "ct03_energy_causality_rep_variant_v0",
        "reference_regime_tag": "CT03_Energy_Causality_Rep_Variant",
        "reference_schema": "CT-03/energy_causality_rep_variant_front_door_report/v1"
      }
    }
  ],
  "schema": "CT-03_energy_causality_rep_variant_comparator/v0",
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
        "CT03_UPDATE_POSITIVE",
        "CT03_UPDATE_NEGATIVE"
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

Record fingerprint: `2936b26f10c5d755c6e08f4a86dd9e4b6182cc00f83e63677592d421fe352ab6`
