# OV-RL-02 - Nonrelativistic NLSE Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted RL02 report artifacts only
- Explicit failure reason taxonomy for grid/limit/dispersion/determinism
- No external truth claim

Reproduce
- Run: `.\py.ps1 -m formal.python.tools.rl02_nonrelativistic_nlse_front_door; .\py.ps1 -m pytest formal/python/tests/test_rl02_nonrelativistic_nlse_v0_lock.py`
- Expected artifacts: `formal/external_evidence/rl02_nonrelativistic_limit_nlse_domain_01/rl02_reference_report.json`, `formal/external_evidence/rl02_nonrelativistic_limit_nlse_domain_01/rl02_candidate_report.json`
- Lock fingerprint must match the value below.

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-09",
  "domain_id": "DRBR-DOMAIN-RL-02",
  "fingerprint": "3d63c28d56dcc8efa49e0212ea20fcb0f3847fe14a00bf819b95d1f55fc80237",
  "inputs": {
    "artifact_dir": "formal/external_evidence/rl02_nonrelativistic_limit_nlse_domain_01",
    "candidate_artifact": "formal/external_evidence/rl02_nonrelativistic_limit_nlse_domain_01/rl02_candidate_report.json",
    "reference_artifact": "formal/external_evidence/rl02_nonrelativistic_limit_nlse_domain_01/rl02_reference_report.json"
  },
  "observable_id": "OV-RL-02",
  "rows": [
    {
      "artifact_id": "RL02_NR_NLSE_LIMIT",
      "diagnostics": {
        "candidate_fingerprint": "29e7b9a234947b26986c9dc2e55275ef06a76d0cda54378c6438c568c050ce98",
        "k_count_candidate": 5,
        "k_count_reference": 5,
        "k_grid_aligned": true,
        "k_grid_order_candidate": true,
        "k_grid_order_reference": true,
        "reference_fingerprint": "86b7d089ecc36c2c30ac47f83c197fad6bb48c0e30d030340263dca3225752fb",
        "scaling_max_abs_candidate": 0.0,
        "scaling_max_abs_reference": 0.0
      },
      "input_data_fingerprint": "29e7b9a234947b26986c9dc2e55275ef06a76d0cda54378c6438c568c050ce98",
      "input_fingerprint": "29e7b9a234947b26986c9dc2e55275ef06a76d0cda54378c6438c568c050ce98",
      "metric_vector": {
        "max_relative_error": 0.0,
        "rel_l2_mismatch": 0.0
      },
      "passed": true,
      "reason_codes": [
        "rl02_nonrelativistic_limit_constraints_satisfied"
      ],
      "source": {
        "candidate_config_tag": "rl02-cand-pinned",
        "candidate_regime_tag": "rl02-lowk",
        "candidate_schema": "RL/nr_nlse_front_door_report/v1",
        "reference_config_tag": "rl02-ref-pinned",
        "reference_regime_tag": "rl02-lowk",
        "reference_schema": "RL/nr_nlse_front_door_report/v1"
      }
    }
  ],
  "schema": "OV-RL-02_nonrelativistic_nlse_comparator/v0",
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
        "RL02_NR_NLSE_LIMIT"
      ]
    },
    "counts": {
      "fail": 0,
      "pass": 1
    }
  },
  "tolerance_profile": "pinned"
}
```

Record fingerprint: `3d63c28d56dcc8efa49e0212ea20fcb0f3847fe14a00bf819b95d1f55fc80237`
