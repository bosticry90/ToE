# OV-BR-FN-01 — Pruning table (BR→FN cross-fit metric residual; summary-only)

Scope / limits
- Summary-only / eliminative-only bookkeeping
- Uses the locked FN-01 cross-fit metric residual report as input
- Unknown is not fail; candidates without declared predictions remain 'unknown'
- No numeric interpretation; structural presence checks only

Record (computed)

```json
{
  "candidate_source": {
    "kind": "declared_surface",
    "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\markdown\\locks\\observables\\OV-BR-FN-00_fn01_metric_residual_prediction_declarations.md",
    "row_key": "candidate_id",
    "source_lock": "OV-BR-FN-00"
  },
  "date": "2026-01-25",
  "fingerprint": "c9d3c4122693e9f0f4dbbc30c3040a527750b638e46945c8f32aba08135ed97b",
  "inputs": {
    "FN-01_cross_fit_metric_residual_DR02_DR03": {
      "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\markdown\\locks\\functionals\\FN-01_cross_fit_metric_residual_DR02_DR03.md",
      "present": true,
      "present_fields": [
        "R_metric",
        "Score",
        "W_FN",
        "epsilon",
        "g_tt_02",
        "g_tt_03"
      ],
      "sha256": "b79f3ed5f2a1e290535d1b7736ff22a8a37c26e7d77c29de13ed616485eea2db"
    },
    "OV-BR-FN-00": {
      "locked_fingerprint": "56d64623fb579a5a5fe30f75fc96dc726680caec96a38d775247274d8f6775c9",
      "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\markdown\\locks\\observables\\OV-BR-FN-00_fn01_metric_residual_prediction_declarations.md",
      "present": true,
      "record_fingerprint": "56d64623fb579a5a5fe30f75fc96dc726680caec96a38d775247274d8f6775c9",
      "schema": "OV-BR-FN-00_fn01_metric_residual_prediction_declarations/v1"
    }
  },
  "observable_id": "OV-BR-FN-01",
  "rows": [
    {
      "candidate_id": "fn01_make_P_cubic_artifact",
      "computed_under_blocked_admissibility": true,
      "reason_codes": [
        "declared_residual_structure_satisfied",
        "computed_under_blocked_admissibility"
      ],
      "survives_br_fn_constraints": "true"
    },
    {
      "candidate_id": "fn01_make_P_cubic_structural_fail_artifact",
      "computed_under_blocked_admissibility": true,
      "reason_codes": [
        "missing_required_residual_fields",
        "missing_fields:__impossible_field__",
        "computed_under_blocked_admissibility"
      ],
      "survives_br_fn_constraints": "false"
    }
  ],
  "schema": "OV-BR-FN-01_fn01_metric_residual_pruning_table/v1",
  "scope_limits": [
    "summary_only",
    "eliminative_only",
    "no_numeric_interpretation",
    "no_new_claims",
    "unknown_is_not_fail",
    "structural_pruning_against_locked_report"
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
      "gate_disabled:CAUS01",
      "input_OV-BR-FN-00_is_blocked"
    ],
    "required_gates": [
      "CT01",
      "SYM01",
      "CAUS01"
    ]
  }
}
```

Record fingerprint: `c9d3c4122693e9f0f4dbbc30c3040a527750b638e46945c8f32aba08135ed97b`
