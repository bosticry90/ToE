# OV-BR-FN-00 — FN metric-residual prediction declarations (structural)

Scope / limits
- Structural-only declaration surface; no physics claim
- Hash-tracks the declaration source file
- Blocked-by-default if source missing

Record (computed)

```json
{
  "date": "2026-01-25",
  "fingerprint": "56d64623fb579a5a5fe30f75fc96dc726680caec96a38d775247274d8f6775c9",
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
      "sha256": "284e1894ea9df1330bfd48c206b76af6e595a872996f2d5fed97b07cd3f0cce3",
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

Record fingerprint: `56d64623fb579a5a5fe30f75fc96dc726680caec96a38d775247274d8f6775c9`
