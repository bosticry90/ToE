# OV-RL-01 - Relativistic Dispersion Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted RL01 report artifacts only
- Explicit failure reason taxonomy for grid/regime/shape/determinism
- No external truth claim

Reproduce
- Run: `.\py.ps1 -m formal.python.tools.rl01_relativistic_dispersion_front_door; .\py.ps1 -m pytest formal/python/tests/test_rl01_relativistic_dispersion_v0_lock.py`
- Expected artifacts: `formal/external_evidence/relativistic_dispersion_domain_01/rl01_reference_report.json`, `formal/external_evidence/relativistic_dispersion_domain_01/rl01_candidate_report.json`
- Lock fingerprint must match the value below.

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-08",
  "domain_id": "DRBR-DOMAIN-RL-01",
  "fingerprint": "22afdda6acea16f05cab9bd2574f358373a4bc1add8e022a53c34a7d5a0f5763",
  "inputs": {
    "artifact_dir": "formal/external_evidence/relativistic_dispersion_domain_01",
    "candidate_artifact": "formal/external_evidence/relativistic_dispersion_domain_01/rl01_candidate_report.json",
    "reference_artifact": "formal/external_evidence/relativistic_dispersion_domain_01/rl01_reference_report.json"
  },
  "observable_id": "OV-RL-01",
  "rows": [
    {
      "artifact_id": "RL01_REL_DISPERSION",
      "diagnostics": {
        "candidate_fingerprint": "3716762ca1a90447e5e359ad7e6c184ff131d7e71f2b4a14c5d0b79fbe4df025",
        "candidate_monotonic_non_decreasing": true,
        "k_count_candidate": 5,
        "k_count_reference": 5,
        "k_grid_aligned": true,
        "k_grid_order_candidate": true,
        "k_grid_order_reference": true,
        "reference_fingerprint": "8bfe00e17bff224cf46a374cf53c901e02397f1230ecb633388f018f49491cdd"
      },
      "input_data_fingerprint": "3716762ca1a90447e5e359ad7e6c184ff131d7e71f2b4a14c5d0b79fbe4df025",
      "input_fingerprint": "3716762ca1a90447e5e359ad7e6c184ff131d7e71f2b4a14c5d0b79fbe4df025",
      "metric_vector": {
        "max_relative_error": 0.0,
        "rel_l2_mismatch": 0.0
      },
      "passed": true,
      "reason_codes": [
        "rl01_relativistic_dispersion_constraints_satisfied"
      ],
      "source": {
        "candidate_config_tag": "rl01-cand-pinned",
        "candidate_regime_tag": "rl01-lowk",
        "candidate_schema": "RL/dispersion_front_door_report/v1",
        "reference_config_tag": "rl01-ref-pinned",
        "reference_regime_tag": "rl01-lowk",
        "reference_schema": "RL/dispersion_front_door_report/v1"
      }
    }
  ],
  "schema": "OV-RL-01_relativistic_dispersion_comparator/v0",
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
        "RL01_REL_DISPERSION"
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

Record fingerprint: `22afdda6acea16f05cab9bd2574f358373a4bc1add8e022a53c34a7d5a0f5763`
