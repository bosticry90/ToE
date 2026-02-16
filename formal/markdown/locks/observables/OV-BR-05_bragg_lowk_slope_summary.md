# OV-BR-05 — Bragg low-k slope summary (computed)

Scope / limits
- Summary-only table derived from locked OV-BR-04A/04B
- Bookkeeping only; no physics claim
- No refitting performed

Record (computed)

```json
{
  "date": "2026-01-25",
  "fingerprint": "5caad193d0c857b5537258776d8fcdf3db1d610695522eeaa96aa881a79354c4",
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
      "manifest_sha256": "284e1894ea9df1330bfd48c206b76af6e595a872996f2d5fed97b07cd3f0cce3",
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

Record fingerprint: `5caad193d0c857b5537258776d8fcdf3db1d610695522eeaa96aa881a79354c4`
