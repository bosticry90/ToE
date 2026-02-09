# OV-BR-SND-03 — Cross-lane low-k consistency audit (computed)

Scope / limits
- Audit only; no physics claim
- Must remain valid even when no Bragg↔Sound mapping exists

Record (computed)

```json
{
  "bragg_date": "2026-01-25",
  "comparability": {
    "reasons": [
      "GATES_DISABLED"
    ],
    "status": "blocked"
  },
  "fingerprint": "3a3d3d8e6e1568b42b75c6cc2e6e733b5b754c7ca40abdaf6e92939a16bf2d11",
  "notes": "Blocked by admissibility manifest; audit not computed.",
  "observable_id": "OV-BR-SND-03",
  "rows": [],
  "schema": "OV-BR-SND-03_cross_lane_lowk_consistency_audit/v4",
  "sound_date": "2026-01-24",
  "source_locators": {},
  "status": {
    "blocked": true,
    "blockers": [
      "admissibility_manifest_blocked"
    ],
    "inputs": {
      "admissibility_manifest": {
        "path": "formal/markdown locks/gates/admissibility_manifest.json",
        "version": 1
      },
      "required_gates": [
        "CT01",
        "SYM01",
        "CAUS01"
      ]
    }
  },
  "status_date": "2026-01-25"
}
```

Record fingerprint: `3a3d3d8e6e1568b42b75c6cc2e6e733b5b754c7ca40abdaf6e92939a16bf2d11`
