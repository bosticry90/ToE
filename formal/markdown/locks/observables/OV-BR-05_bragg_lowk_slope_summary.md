# OV-BR-05 — Bragg low-k slope summary (computed)

Scope / limits
- Summary-only table derived from locked OV-BR-04A/04B
- Bookkeeping only; no physics claim
- No refitting performed

Record (computed)

```json
{
  "date": "2026-01-25",
  "fingerprint": "bcd8661f9fafef7c901fa830f6a1eb0012ca64de4dc0267d0eb9144eb4f0c9d6",
  "inputs": {},
  "observable_id": "OV-BR-05",
  "rows": [
    {
      "c_mm_per_s": null,
      "condition_key": "condition_A",
      "condition_semantic": "blocked_placeholder",
      "se_mm_per_s": null
    },
    {
      "c_mm_per_s": null,
      "condition_key": "condition_B",
      "condition_semantic": "blocked_placeholder",
      "se_mm_per_s": null
    }
  ],
  "schema": "OV-BR-05_bragg_lowk_slope_summary/v1",
  "scope_limits": [
    "blocked_by_admissibility_manifest",
    "requires_CT01_SYM01_CAUS01",
    "structural_placeholder_only_when_blocked"
  ],
  "selection": {},
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
  }
}
```

Record fingerprint: `bcd8661f9fafef7c901fa830f6a1eb0012ca64de4dc0267d0eb9144eb4f0c9d6`
