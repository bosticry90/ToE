# OV-RL-11 - Causality Signal-Cone Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted RL11 report artifacts only
- Expectation-aware pass semantics for positive/negative controls
- No external truth claim

Reproduce (pinned)
- Command: `.\py.ps1 -m formal.python.tools.rl11_causality_signal_cone_front_door`
- Outputs: `formal/external_evidence/rl11_causality_signal_cone_domain_01/rl11_reference_report.json`, `formal/external_evidence/rl11_causality_signal_cone_domain_01/rl11_candidate_report.json`
- Verify: `.\py.ps1 -m pytest formal/python/tests/test_rl11_causality_signal_cone_v0_lock.py -q`

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-09",
  "domain_id": "DRBR-DOMAIN-RL-11",
  "fingerprint": "b8b9a3150a3bec7c42c402773fe473fd537a3d0d2cd50ef8ba3f35d6ca842814",
  "inputs": {
    "artifact_dir": "formal/external_evidence/rl11_causality_signal_cone_domain_01",
    "candidate_artifact": "formal/external_evidence/rl11_causality_signal_cone_domain_01/rl11_candidate_report.json",
    "reference_artifact": "formal/external_evidence/rl11_causality_signal_cone_domain_01/rl11_reference_report.json"
  },
  "observable_id": "OV-RL-11",
  "rows": [
    {
      "artifact_id": "RL11_CAUSALITY_POSITIVE",
      "diagnostics": {
        "candidate_fingerprint": "8f022f21fccfcaf8f32f3d30da163820ff3ec5a11afc0534d7d85a602c4e8615",
        "reference_fingerprint": "c9c81fb9e9ce8ac989b3404acddd575fede8dba80126ceff94b35ef5a992809b",
        "x_count_candidate": 256,
        "x_count_reference": 256,
        "x_grid_aligned": true
      },
      "input_data_fingerprint": "8f022f21fccfcaf8f32f3d30da163820ff3ec5a11afc0534d7d85a602c4e8615",
      "input_fingerprint": "8f022f21fccfcaf8f32f3d30da163820ff3ec5a11afc0534d7d85a602c4e8615",
      "metric_vector": {
        "cfl": 0.4074366543152521,
        "cfl_max": 1.0,
        "eps_acausal": 0.001,
        "eps_causal": 1e-10,
        "leakage_outside_cone": 0.0,
        "radius": 0.1
      },
      "passed": true,
      "reason_codes": [
        "rl11_causality_cone_ok"
      ],
      "source": {
        "candidate_config_tag": "rl11-cand-pinned",
        "candidate_regime_tag": "rl11-causality-signal-cone",
        "candidate_schema": "RL/causality_signal_cone_front_door_report/v1",
        "case_id": "POSITIVE",
        "case_kind": "positive_control",
        "reference_config_tag": "rl11-ref-pinned",
        "reference_regime_tag": "rl11-causality-signal-cone",
        "reference_schema": "RL/causality_signal_cone_front_door_report/v1"
      }
    },
    {
      "artifact_id": "RL11_CAUSALITY_NEGATIVE",
      "diagnostics": {
        "candidate_fingerprint": "8f022f21fccfcaf8f32f3d30da163820ff3ec5a11afc0534d7d85a602c4e8615",
        "reference_fingerprint": "c9c81fb9e9ce8ac989b3404acddd575fede8dba80126ceff94b35ef5a992809b",
        "x_count_candidate": 256,
        "x_count_reference": 256,
        "x_grid_aligned": true
      },
      "input_data_fingerprint": "8f022f21fccfcaf8f32f3d30da163820ff3ec5a11afc0534d7d85a602c4e8615",
      "input_fingerprint": "8f022f21fccfcaf8f32f3d30da163820ff3ec5a11afc0534d7d85a602c4e8615",
      "metric_vector": {
        "cfl": 2.0371832715762603,
        "cfl_max": 1.0,
        "eps_acausal": 0.001,
        "eps_causal": 1e-10,
        "leakage_outside_cone": 0.004999999999999999,
        "radius": 0.5
      },
      "passed": true,
      "reason_codes": [
        "rl11_acausal_leakage_detected"
      ],
      "source": {
        "candidate_config_tag": "rl11-cand-pinned",
        "candidate_regime_tag": "rl11-causality-signal-cone",
        "candidate_schema": "RL/causality_signal_cone_front_door_report/v1",
        "case_id": "NEGATIVE",
        "case_kind": "negative_control",
        "reference_config_tag": "rl11-ref-pinned",
        "reference_regime_tag": "rl11-causality-signal-cone",
        "reference_schema": "RL/causality_signal_cone_front_door_report/v1"
      }
    }
  ],
  "schema": "OV-RL-11_causality_signal_cone_comparator/v0",
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
        "RL11_CAUSALITY_POSITIVE",
        "RL11_CAUSALITY_NEGATIVE"
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

Record fingerprint: `b8b9a3150a3bec7c42c402773fe473fd537a3d0d2cd50ef8ba3f35d6ca842814`
