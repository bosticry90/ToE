# OV-RL-10 - Entropy Balance Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted RL10 report artifacts only
- Expectation-aware pass semantics for positive/negative controls
- No external truth claim

Reproduce (pinned)
- Command: `.\py.ps1 -m formal.python.tools.rl10_entropy_balance_front_door`
- Outputs: `formal/external_evidence/rl10_entropy_balance_domain_01/rl10_reference_report.json`, `formal/external_evidence/rl10_entropy_balance_domain_01/rl10_candidate_report.json`
- Verify: `.\py.ps1 -m pytest formal/python/tests/test_rl10_entropy_balance_v0_lock.py -q`

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-09",
  "domain_id": "DRBR-DOMAIN-RL-10",
  "fingerprint": "32669debcbb02f608528d5a15b7715bfc4b5fca4a69214f7c1d3da36ba6fc144",
  "inputs": {
    "artifact_dir": "formal/external_evidence/rl10_entropy_balance_domain_01",
    "candidate_artifact": "formal/external_evidence/rl10_entropy_balance_domain_01/rl10_candidate_report.json",
    "reference_artifact": "formal/external_evidence/rl10_entropy_balance_domain_01/rl10_reference_report.json"
  },
  "observable_id": "OV-RL-10",
  "rows": [
    {
      "artifact_id": "RL10_ENTROPY_POSITIVE",
      "diagnostics": {
        "candidate_fingerprint": "8059f07533ec42252853866124c687cc2d89e1d0d81e4ed85bee29d194b3a96f",
        "reference_fingerprint": "bd0e07f05986106cad9cbc95a46f123cd2a818031e26cdbe975decb672b2f043"
      },
      "input_data_fingerprint": "8059f07533ec42252853866124c687cc2d89e1d0d81e4ed85bee29d194b3a96f",
      "input_fingerprint": "8059f07533ec42252853866124c687cc2d89e1d0d81e4ed85bee29d194b3a96f",
      "metric_vector": {
        "db_residual": 5.551115123125783e-17,
        "eps_balance": 1e-08,
        "eps_entropy": 0.001,
        "sigma_proxy": 7.401486830834381e-18
      },
      "passed": true,
      "reason_codes": [
        "rl10_entropy_balance_ok"
      ],
      "source": {
        "candidate_config_tag": "rl10-cand-pinned",
        "candidate_regime_tag": "rl10-entropy-balance",
        "candidate_schema": "RL/entropy_balance_front_door_report/v1",
        "case_id": "POSITIVE",
        "case_kind": "positive_control",
        "reference_config_tag": "rl10-ref-pinned",
        "reference_regime_tag": "rl10-entropy-balance",
        "reference_schema": "RL/entropy_balance_front_door_report/v1"
      }
    },
    {
      "artifact_id": "RL10_ENTROPY_NEGATIVE",
      "diagnostics": {
        "candidate_fingerprint": "8059f07533ec42252853866124c687cc2d89e1d0d81e4ed85bee29d194b3a96f",
        "reference_fingerprint": "bd0e07f05986106cad9cbc95a46f123cd2a818031e26cdbe975decb672b2f043"
      },
      "input_data_fingerprint": "8059f07533ec42252853866124c687cc2d89e1d0d81e4ed85bee29d194b3a96f",
      "input_fingerprint": "8059f07533ec42252853866124c687cc2d89e1d0d81e4ed85bee29d194b3a96f",
      "metric_vector": {
        "db_residual": 0.0666666666666667,
        "eps_balance": 1e-08,
        "eps_entropy": 0.001,
        "sigma_proxy": 0.32188758248682003
      },
      "passed": true,
      "reason_codes": [
        "rl10_entropy_production_detected"
      ],
      "source": {
        "candidate_config_tag": "rl10-cand-pinned",
        "candidate_regime_tag": "rl10-entropy-balance",
        "candidate_schema": "RL/entropy_balance_front_door_report/v1",
        "case_id": "NEGATIVE",
        "case_kind": "negative_control",
        "reference_config_tag": "rl10-ref-pinned",
        "reference_regime_tag": "rl10-entropy-balance",
        "reference_schema": "RL/entropy_balance_front_door_report/v1"
      }
    }
  ],
  "schema": "OV-RL-10_entropy_balance_comparator/v0",
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
        "RL10_ENTROPY_POSITIVE",
        "RL10_ENTROPY_NEGATIVE"
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

Record fingerprint: `32669debcbb02f608528d5a15b7715bfc4b5fca4a69214f7c1d3da36ba6fc144`
