# OV-BR-FN-00 — FN metric-residual prediction declarations (structural)

Scope / limits
- Structural-only declaration surface; no physics claim
- Hash-tracks the declaration source file
- Blocked-by-default if source missing

Record (computed)

```json
{
  "date": "2026-01-25",
  "fingerprint": "bdd185ecd71754aeb07c975a2b1d34e3388b9be8b5333a4f688aac257a7ab195",
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
    "no_new_claims"
  ],
  "status": {
    "admissibility_manifest": {
      "path": "formal/markdown locks/gates/admissibility_manifest_ENABLED_OVERRIDE.json",
      "sha256": "2f9c1aa1dbcc30451ac0740cb09d85c1d12b6490efb02d449e453cc0de94c13f",
      "version": 5
    },
    "blocked": false,
    "reasons": [],
    "required_gates": [
      "CT01",
      "SYM01",
      "CAUS01"
    ]
  }
}
```

Record fingerprint: `bdd185ecd71754aeb07c975a2b1d34e3388b9be8b5333a4f688aac257a7ab195`
