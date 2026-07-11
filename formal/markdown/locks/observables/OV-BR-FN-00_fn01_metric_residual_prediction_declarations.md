# OV-BR-FN-00 — FN metric-residual prediction declarations (structural)

Scope / limits
- Structural-only declaration surface; no physics claim
- Hash-tracks the declaration source file
- Blocked-by-default if source missing

Record (computed)

```json
{
  "date": "2026-01-25",
  "fingerprint": "66db034f3259b2e612dc8d2b0ec4b4bf8ec53da01326b677d60f1c1fad294c45",
  "inputs": {
    "candidate_source": {
      "extraction_rule": "collect FunctionDef names matching prefix+suffix; sorted lexicographically",
      "function_prefix": "fn01_make_",
      "function_suffix": "_artifact",
      "kind": "python_ast",
      "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\python\\toe\\constraints\\fn01_artifact.py"
    },
    "declarations": {
      "expected_path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\python\\toe\\bridges\\brfn01_prediction_declarations.json",
      "extra_candidate_ids": [],
      "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\python\\toe\\bridges\\brfn01_prediction_declarations.json",
      "present": true,
      "raw_sha256": "2406e3f837778030f5a466530c08b6857cc4a3ac4d1fc2b5007bce821fef304d",
      "schema": "BRFN01_prediction_declarations/v1",
      "version": 1
    }
  },
  "observable_id": "OV-BR-FN-00",
  "rows": [
    {
      "candidate_id": "fn01_make_P_cubic_artifact",
      "declared": true,
      "prediction": {
        "kind": "fn01_metric_residual_fields_required",
        "required_fields": [
          "g_tt_02",
          "g_tt_03",
          "R_metric",
          "Score"
        ]
      },
      "prediction_kind": "fn01_metric_residual_fields_required"
    },
    {
      "candidate_id": "fn01_make_P_cubic_structural_fail_artifact",
      "declared": true,
      "prediction": {
        "kind": "fn01_metric_residual_fields_required",
        "required_fields": [
          "g_tt_02",
          "g_tt_03",
          "R_metric",
          "Score",
          "__impossible_field__"
        ]
      },
      "prediction_kind": "fn01_metric_residual_fields_required"
    }
  ],
  "schema": "OV-BR-FN-00_fn01_metric_residual_prediction_declarations/v1",
  "scope_limits": [
    "structural_only",
    "hash_tracked_declaration_source",
    "no_new_claims",
    "blocked_by_admissibility_manifest",
    "requires_CT01_SYM01_CAUS01"
  ],
  "status": {
    "admissibility_manifest": {
      "path": "formal/markdown locks/gates/admissibility_manifest.json",
      "sha256": "bf44287823ccbff8dc66260fb95611e5c44f4b8076d33a6d6e2072dc95be1a19",
      "version": 1
    },
    "blocked": true,
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

Record fingerprint: `66db034f3259b2e612dc8d2b0ec4b4bf8ec53da01326b677d60f1c1fad294c45`
