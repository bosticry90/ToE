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
    "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\markdown\\locks\\observables\\OV-BR-FN-00_fn01_metric_residual_prediction_declarations_OVERRIDE.md",
    "row_key": "candidate_id",
    "source_lock": "OV-BR-FN-00"
  },
  "date": "2026-01-25",
  "fingerprint": "b3b7e410ee594c5eb9d4f0061b0b3daa0f653b47d6f207d4bcc3f18dc8ce4597",
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
      "locked_fingerprint": "bdd185ecd71754aeb07c975a2b1d34e3388b9be8b5333a4f688aac257a7ab195",
      "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\markdown\\locks\\observables\\OV-BR-FN-00_fn01_metric_residual_prediction_declarations_OVERRIDE.md",
      "present": true,
      "record_fingerprint": "bdd185ecd71754aeb07c975a2b1d34e3388b9be8b5333a4f688aac257a7ab195",
      "schema": "OV-BR-FN-00_fn01_metric_residual_prediction_declarations/v1"
    }
  },
  "observable_id": "OV-BR-FN-01",
  "rows": [
    {
      "candidate_id": "fn01_make_P_cubic_artifact",
      "computed_under_blocked_admissibility": false,
      "reason_codes": [
        "declared_residual_structure_satisfied"
      ],
      "survives_br_fn_constraints": "true"
    },
    {
      "candidate_id": "fn01_make_P_cubic_structural_fail_artifact",
      "computed_under_blocked_admissibility": false,
      "reason_codes": [
        "missing_required_residual_fields",
        "missing_fields:__impossible_field__"
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

Record fingerprint: `b3b7e410ee594c5eb9d4f0061b0b3daa0f653b47d6f207d4bcc3f18dc8ce4597`
