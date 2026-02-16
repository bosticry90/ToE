# OV-RL-05 - Wave Equation Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted RL05 report artifacts only
- Explicit failure reason taxonomy for grid/wave residual/determinism
- No external truth claim

Reproduce
- Run: `.\py.ps1 -m formal.python.tools.rl05_wave_equation_front_door; .\py.ps1 -m pytest formal/python/tests/test_rl05_wave_equation_v0_lock.py`
- Expected artifacts: `formal/external_evidence/rl05_wave_equation_domain_01/rl05_reference_report.json`, `formal/external_evidence/rl05_wave_equation_domain_01/rl05_candidate_report.json`
- Lock fingerprint must match the value below.

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-09",
  "domain_id": "DRBR-DOMAIN-RL-05",
  "fingerprint": "e86a2f325899ab8110a628d5ee3df86287c8cffc458cb11d0a63afddbc50a3c7",
  "inputs": {
    "artifact_dir": "formal/external_evidence/rl05_wave_equation_domain_01",
    "candidate_artifact": "formal/external_evidence/rl05_wave_equation_domain_01/rl05_candidate_report.json",
    "reference_artifact": "formal/external_evidence/rl05_wave_equation_domain_01/rl05_reference_report.json"
  },
  "observable_id": "OV-RL-05",
  "rows": [
    {
      "artifact_id": "RL05_WAVE_EQUATION",
      "diagnostics": {
        "candidate_fingerprint": "bb8590456ee1bf9239a08fb85d992ad278d42075a81b425f35615139e2ceec3c",
        "reference_fingerprint": "24e7e1d820dcab814f978f5a49c7aa2ef75724fee363dd23b17459b46c369135",
        "t_count_candidate": 32,
        "t_count_reference": 32,
        "t_grid_aligned": true,
        "t_grid_order_candidate": true,
        "t_grid_order_reference": true,
        "x_count_candidate": 128,
        "x_count_reference": 128,
        "x_grid_aligned": true,
        "x_grid_order_candidate": true,
        "x_grid_order_reference": true
      },
      "input_data_fingerprint": "bb8590456ee1bf9239a08fb85d992ad278d42075a81b425f35615139e2ceec3c",
      "input_fingerprint": "bb8590456ee1bf9239a08fb85d992ad278d42075a81b425f35615139e2ceec3c",
      "metric_vector": {
        "residual_l2_ratio": 0.000632401091182465,
        "residual_linf_abs": 0.0006322741048441216
      },
      "passed": false,
      "reason_codes": [
        "FAIL_WAVE_RESIDUAL"
      ],
      "source": {
        "candidate_config_tag": "rl05-cand-pinned",
        "candidate_regime_tag": "rl05-wave",
        "candidate_schema": "RL/wave_equation_front_door_report/v1",
        "reference_config_tag": "rl05-ref-pinned",
        "reference_regime_tag": "rl05-wave",
        "reference_schema": "RL/wave_equation_front_door_report/v1"
      }
    }
  ],
  "schema": "OV-RL-05_wave_equation_comparator/v0",
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
      "fail": [
        "RL05_WAVE_EQUATION"
      ],
      "pass": []
    },
    "counts": {
      "fail": 1,
      "pass": 0
    }
  },
  "tolerance_profile": "pinned"
}
```

Record fingerprint: `e86a2f325899ab8110a628d5ee3df86287c8cffc458cb11d0a63afddbc50a3c7`
