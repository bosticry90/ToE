# OV-RL-06 - Phase Winding Quantization Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted RL06 report artifacts only
- Explicit failure reason taxonomy for grid/winding/determinism
- No external truth claim

Reproduce
- Run: `.\py.ps1 -m formal.python.tools.rl06_phase_winding_quantization_front_door; .\py.ps1 -m pytest formal/python/tests/test_rl06_phase_winding_quantization_v0_lock.py`
- Expected artifacts: `formal/external_evidence/rl06_phase_winding_quantization_domain_01/rl06_reference_report.json`, `formal/external_evidence/rl06_phase_winding_quantization_domain_01/rl06_candidate_report.json`
- Lock fingerprint must match the value below.

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-09",
  "domain_id": "DRBR-DOMAIN-RL-06",
  "fingerprint": "9125be83fc0e6ad181af3567885e1bf8829fdfcc80582d6599c04e235a5f3a01",
  "inputs": {
    "artifact_dir": "formal/external_evidence/rl06_phase_winding_quantization_domain_01",
    "candidate_artifact": "formal/external_evidence/rl06_phase_winding_quantization_domain_01/rl06_candidate_report.json",
    "reference_artifact": "formal/external_evidence/rl06_phase_winding_quantization_domain_01/rl06_reference_report.json"
  },
  "observable_id": "OV-RL-06",
  "rows": [
    {
      "artifact_id": "RL06_WINDING_QUANTIZED",
      "diagnostics": {
        "candidate_fingerprint": "eb0d88604e93008f51aabfa0133c72d7ba87c86c683d913f60a87d456ca31107",
        "reference_fingerprint": "57efb42e743f73e6128cf57b17c54ba813619ea9eab8c0b59c7dac650647cf76",
        "x_count_candidate": 128,
        "x_count_reference": 128,
        "x_grid_aligned": true,
        "x_grid_order_candidate": true,
        "x_grid_order_reference": true
      },
      "input_data_fingerprint": "eb0d88604e93008f51aabfa0133c72d7ba87c86c683d913f60a87d456ca31107",
      "input_fingerprint": "eb0d88604e93008f51aabfa0133c72d7ba87c86c683d913f60a87d456ca31107",
      "metric_vector": {
        "delta_int": 0.015625,
        "winding": 1.984375
      },
      "passed": false,
      "reason_codes": [
        "FAIL_WINDING_NOT_INTEGER"
      ],
      "source": {
        "candidate_config_tag": "rl06-cand-pinned",
        "candidate_regime_tag": "rl06-phase-winding",
        "candidate_schema": "RL/phase_winding_front_door_report/v1",
        "case_id": "QUANTIZED",
        "case_kind": "quantized",
        "reference_config_tag": "rl06-ref-pinned",
        "reference_regime_tag": "rl06-phase-winding",
        "reference_schema": "RL/phase_winding_front_door_report/v1"
      }
    },
    {
      "artifact_id": "RL06_WINDING_NONINT",
      "diagnostics": {
        "candidate_fingerprint": "eb0d88604e93008f51aabfa0133c72d7ba87c86c683d913f60a87d456ca31107",
        "reference_fingerprint": "57efb42e743f73e6128cf57b17c54ba813619ea9eab8c0b59c7dac650647cf76",
        "x_count_candidate": 128,
        "x_count_reference": 128,
        "x_grid_aligned": true,
        "x_grid_order_candidate": true,
        "x_grid_order_reference": true
      },
      "input_data_fingerprint": "eb0d88604e93008f51aabfa0133c72d7ba87c86c683d913f60a87d456ca31107",
      "input_fingerprint": "eb0d88604e93008f51aabfa0133c72d7ba87c86c683d913f60a87d456ca31107",
      "metric_vector": {
        "delta_int": 0.33164062500000036,
        "winding": 2.3316406250000004
      },
      "passed": true,
      "reason_codes": [
        "rl06_phase_winding_negative_control_detected"
      ],
      "source": {
        "candidate_config_tag": "rl06-cand-pinned",
        "candidate_regime_tag": "rl06-phase-winding",
        "candidate_schema": "RL/phase_winding_front_door_report/v1",
        "case_id": "NONINT",
        "case_kind": "negative_control",
        "reference_config_tag": "rl06-ref-pinned",
        "reference_regime_tag": "rl06-phase-winding",
        "reference_schema": "RL/phase_winding_front_door_report/v1"
      }
    }
  ],
  "schema": "OV-RL-06_phase_winding_quantization_comparator/v0",
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
        "RL06_WINDING_QUANTIZED"
      ],
      "pass": [
        "RL06_WINDING_NONINT"
      ]
    },
    "counts": {
      "fail": 1,
      "pass": 1
    }
  },
  "tolerance_profile": "pinned"
}
```

Record fingerprint: `9125be83fc0e6ad181af3567885e1bf8829fdfcc80582d6599c04e235a5f3a01`
