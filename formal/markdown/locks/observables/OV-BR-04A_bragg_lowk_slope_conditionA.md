# OV-BR-04A — Bragg low-k slope (condition_A) (computed)

Scope / limits
- Derived from frozen OV-BR-03N points only
- Deterministic low-k window + pinned slope rule
- Bookkeeping / anchoring only; no ToE validation claim

Record (computed)

```json
{
  "condition_key": "condition_A",
  "condition_semantic": "blocked",
  "date": "2026-01-25",
  "fingerprint": "99b210f200598b688c7ee936c53cdc657809248d030665f8e7ddd891ae3d1caa",
  "input_dataset": {},
  "method": {},
  "observable_id": "OV-BR-04A",
  "results": {},
  "schema": "OV-BR-04A_bragg_lowk_slope_conditionA/v2",
  "scope_limits": [
    "blocked_by_admissibility_manifest",
    "requires_CT01_SYM01_CAUS01"
  ],
  "selection": {
    "parameters": {
      "k_um_inv_max": 1.0,
      "omega_over_2pi_kHz_max": 1.3,
      "omega_over_2pi_kHz_min": 0.1
    },
    "rule_id": "lowk_window_v1"
  },
  "status": {
    "admissibility_manifest": {
      "path": "formal/markdown locks/gates/admissibility_manifest.json",
      "version": 1
    },
    "blocked": true,
    "debug": {
      "manifest_input_path": null,
      "manifest_resolved_path": "formal/markdown locks/gates/admissibility_manifest.json",
      "manifest_sha256": "99a290146c803db75d94be40c656db8f00afb59fd60d4d76b9640e8a3cbbc750",
      "manifest_version": 1
    },
    "reasons": [
      "gate_disabled:CT01",
      "gate_disabled:SYM01",
      "gate_disabled:CAUS01"
    ],
    "required_gates": [
      "CT01",
      "SYM01",
      "CAUS01"
    ]
  },
  "units": {}
}
```

Record fingerprint: `99b210f200598b688c7ee936c53cdc657809248d030665f8e7ddd891ae3d1caa`
