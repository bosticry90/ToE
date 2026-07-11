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
  "fingerprint": "9516507f005376bd65e58ddeb5cd4a8720ea4593e289a75b9284235304f95e14",
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
      "manifest_sha256": "bf44287823ccbff8dc66260fb95611e5c44f4b8076d33a6d6e2072dc95be1a19",
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

Record fingerprint: `9516507f005376bd65e58ddeb5cd4a8720ea4593e289a75b9284235304f95e14`
