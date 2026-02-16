# OV-RL-07 - Energy/Noether Conservation Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted RL07 report artifacts only
- Expectation-aware pass semantics for positive/negative controls
- No external truth claim

Reproduce (pinned)
- Command: `.\py.ps1 -m formal.python.tools.rl07_energy_noether_conservation_front_door`
- Outputs: `formal/external_evidence/rl07_energy_noether_conservation_domain_01/rl07_reference_report.json`, `formal/external_evidence/rl07_energy_noether_conservation_domain_01/rl07_candidate_report.json`
- Verify: `.\py.ps1 -m pytest formal/python/tests/test_rl07_energy_noether_conservation_v0_lock.py -q`

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-09",
  "domain_id": "DRBR-DOMAIN-RL-07",
  "fingerprint": "7a4dd0a64791b15ce14ed355135e5bbd97429e1bc174a7b6ba3e5edd68687b84",
  "inputs": {
    "artifact_dir": "formal/external_evidence/rl07_energy_noether_conservation_domain_01",
    "candidate_artifact": "formal/external_evidence/rl07_energy_noether_conservation_domain_01/rl07_candidate_report.json",
    "reference_artifact": "formal/external_evidence/rl07_energy_noether_conservation_domain_01/rl07_reference_report.json"
  },
  "observable_id": "OV-RL-07",
  "rows": [
    {
      "artifact_id": "RL07_ENERGY_POSITIVE",
      "diagnostics": {
        "candidate_fingerprint": "870b0be9f8205534c4f6ad6cae72e94dd20fa3bcf7d3a86196af539dc8b087cb",
        "reference_fingerprint": "4d9b212a87d073b0894ec8469435cd7a8805712a6d02b77bf4ec9ad2c034453f",
        "x_count_candidate": 128,
        "x_count_reference": 128,
        "x_grid_aligned": true,
        "x_grid_order_candidate": true,
        "x_grid_order_reference": true
      },
      "input_data_fingerprint": "870b0be9f8205534c4f6ad6cae72e94dd20fa3bcf7d3a86196af539dc8b087cb",
      "input_fingerprint": "870b0be9f8205534c4f6ad6cae72e94dd20fa3bcf7d3a86196af539dc8b087cb",
      "metric_vector": {
        "e0": 1.5695350834348565,
        "et": 1.569671570277277,
        "max_rel_drift": 0.0005966084844298418,
        "rel_drift": 8.696004559631644e-05,
        "rel_drop": -8.696004559631644e-05
      },
      "passed": true,
      "reason_codes": [
        "rl07_energy_conservation_ok"
      ],
      "source": {
        "candidate_config_tag": "rl07-cand-pinned",
        "candidate_regime_tag": "rl07-energy-noether",
        "candidate_schema": "RL/energy_noether_front_door_report/v1",
        "case_id": "POSITIVE",
        "case_kind": "positive_control",
        "reference_config_tag": "rl07-ref-pinned",
        "reference_regime_tag": "rl07-energy-noether",
        "reference_schema": "RL/energy_noether_front_door_report/v1"
      }
    },
    {
      "artifact_id": "RL07_ENERGY_NEGATIVE",
      "diagnostics": {
        "candidate_fingerprint": "870b0be9f8205534c4f6ad6cae72e94dd20fa3bcf7d3a86196af539dc8b087cb",
        "reference_fingerprint": "4d9b212a87d073b0894ec8469435cd7a8805712a6d02b77bf4ec9ad2c034453f",
        "x_count_candidate": 128,
        "x_count_reference": 128,
        "x_grid_aligned": true,
        "x_grid_order_candidate": true,
        "x_grid_order_reference": true
      },
      "input_data_fingerprint": "870b0be9f8205534c4f6ad6cae72e94dd20fa3bcf7d3a86196af539dc8b087cb",
      "input_fingerprint": "870b0be9f8205534c4f6ad6cae72e94dd20fa3bcf7d3a86196af539dc8b087cb",
      "metric_vector": {
        "e0": 1.5695350834348565,
        "et": 1.2989706114545443,
        "max_rel_drift": 0.1723851061603504,
        "rel_drift": 0.1723851061603504,
        "rel_drop": 0.1723851061603504
      },
      "passed": true,
      "reason_codes": [
        "rl07_energy_drop_detected"
      ],
      "source": {
        "candidate_config_tag": "rl07-cand-pinned",
        "candidate_regime_tag": "rl07-energy-noether",
        "candidate_schema": "RL/energy_noether_front_door_report/v1",
        "case_id": "NEGATIVE",
        "case_kind": "negative_control",
        "reference_config_tag": "rl07-ref-pinned",
        "reference_regime_tag": "rl07-energy-noether",
        "reference_schema": "RL/energy_noether_front_door_report/v1"
      }
    }
  ],
  "schema": "OV-RL-07_energy_noether_conservation_comparator/v0",
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
        "RL07_ENERGY_POSITIVE",
        "RL07_ENERGY_NEGATIVE"
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

Record fingerprint: `7a4dd0a64791b15ce14ed355135e5bbd97429e1bc174a7b6ba3e5edd68687b84`
