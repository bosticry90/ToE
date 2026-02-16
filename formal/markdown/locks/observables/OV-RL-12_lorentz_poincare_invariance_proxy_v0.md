# OV-RL-12 - Lorentz/Poincare Invariance Proxy Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted RL12 report artifacts only
- Expectation-aware pass semantics for positive/negative controls
- No external truth claim

Reproduce (pinned)
- Command: `.\py.ps1 -m formal.python.tools.rl12_lorentz_poincare_invariance_proxy_front_door`
- Outputs: `formal/external_evidence/rl12_lorentz_poincare_invariance_proxy_domain_01/rl12_reference_report.json`, `formal/external_evidence/rl12_lorentz_poincare_invariance_proxy_domain_01/rl12_candidate_report.json`
- Verify: `.\py.ps1 -m pytest formal/python/tests/test_rl12_lorentz_poincare_invariance_proxy_v0_lock.py -q`

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-09",
  "domain_id": "DRBR-DOMAIN-RL-12",
  "fingerprint": "f78caab7f9892a846958ddc18409486b039070d82a65c9138482794513907e5c",
  "inputs": {
    "artifact_dir": "formal/external_evidence/rl12_lorentz_poincare_invariance_proxy_domain_01",
    "candidate_artifact": "formal/external_evidence/rl12_lorentz_poincare_invariance_proxy_domain_01/rl12_candidate_report.json",
    "reference_artifact": "formal/external_evidence/rl12_lorentz_poincare_invariance_proxy_domain_01/rl12_reference_report.json"
  },
  "observable_id": "OV-RL-12",
  "rows": [
    {
      "artifact_id": "RL12_LORENTZ_positive_control",
      "diagnostics": {
        "candidate_fingerprint": "792998efbdf173758f30ff1cdc9473e65c6a86db5e3a6da9d0586bf7b05a9af1",
        "grid_aligned": true,
        "reference_fingerprint": "792998efbdf173758f30ff1cdc9473e65c6a86db5e3a6da9d0586bf7b05a9af1",
        "t_count_candidate": 128,
        "t_count_reference": 128,
        "x_count_candidate": 256,
        "x_count_reference": 256
      },
      "input_data_fingerprint": "792998efbdf173758f30ff1cdc9473e65c6a86db5e3a6da9d0586bf7b05a9af1",
      "input_fingerprint": "792998efbdf173758f30ff1cdc9473e65c6a86db5e3a6da9d0586bf7b05a9af1",
      "metric_vector": {
        "eps_break": 0.001,
        "eps_invariant": 1e-08,
        "invariant_metric": 3.2197198066877327e-16
      },
      "passed": true,
      "reason_codes": [
        "rl12_lorentz_invariance_ok"
      ],
      "source": {
        "candidate_config_tag": "rl12_lorentz_poincare_invariance_proxy_v0",
        "candidate_regime_tag": "RL12_Lorentz_Poincare_Invariance_Proxy",
        "candidate_schema": "RL/lorentz_poincare_invariance_front_door_report/v1",
        "case_id": "positive_control",
        "case_kind": "positive_control",
        "reference_config_tag": "rl12_lorentz_poincare_invariance_proxy_v0",
        "reference_regime_tag": "RL12_Lorentz_Poincare_Invariance_Proxy",
        "reference_schema": "RL/lorentz_poincare_invariance_front_door_report/v1"
      }
    },
    {
      "artifact_id": "RL12_LORENTZ_negative_control",
      "diagnostics": {
        "candidate_fingerprint": "792998efbdf173758f30ff1cdc9473e65c6a86db5e3a6da9d0586bf7b05a9af1",
        "grid_aligned": true,
        "reference_fingerprint": "792998efbdf173758f30ff1cdc9473e65c6a86db5e3a6da9d0586bf7b05a9af1",
        "t_count_candidate": 128,
        "t_count_reference": 128,
        "x_count_candidate": 256,
        "x_count_reference": 256
      },
      "input_data_fingerprint": "792998efbdf173758f30ff1cdc9473e65c6a86db5e3a6da9d0586bf7b05a9af1",
      "input_fingerprint": "792998efbdf173758f30ff1cdc9473e65c6a86db5e3a6da9d0586bf7b05a9af1",
      "metric_vector": {
        "eps_break": 0.001,
        "eps_invariant": 1e-08,
        "invariant_metric": 0.362216562583028
      },
      "passed": true,
      "reason_codes": [
        "rl12_invariance_break_detected"
      ],
      "source": {
        "candidate_config_tag": "rl12_lorentz_poincare_invariance_proxy_v0",
        "candidate_regime_tag": "RL12_Lorentz_Poincare_Invariance_Proxy",
        "candidate_schema": "RL/lorentz_poincare_invariance_front_door_report/v1",
        "case_id": "negative_control",
        "case_kind": "negative_control",
        "reference_config_tag": "rl12_lorentz_poincare_invariance_proxy_v0",
        "reference_regime_tag": "RL12_Lorentz_Poincare_Invariance_Proxy",
        "reference_schema": "RL/lorentz_poincare_invariance_front_door_report/v1"
      }
    }
  ],
  "schema": "OV-RL-12_lorentz_poincare_invariance_proxy_comparator/v0",
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
        "RL12_LORENTZ_positive_control",
        "RL12_LORENTZ_negative_control"
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

Record fingerprint: `f78caab7f9892a846958ddc18409486b039070d82a65c9138482794513907e5c`
