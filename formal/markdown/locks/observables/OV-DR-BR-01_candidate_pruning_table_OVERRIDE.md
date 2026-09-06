# OV-DR-BR-01 — Candidate pruning table (DR-01 → BR-01; summary-only)

Scope / limits
- Summary-only / eliminative-only bookkeeping
- Uses OV-BR-05 as the single canonical Bragg input
- Unknown is not fail; candidates without declared predictions remain 'unknown'
- No numeric interpretation; no new claims

Record (computed)

```json
{
  "candidate_source": {
    "extraction_rule": "collect FunctionDef names with prefix; sorted lexicographically",
    "function_prefix": "BR01_",
    "kind": "python_ast",
    "path": "formal/python/toe/bridges/br01_candidates.py"
  },
  "date": "2026-01-25",
  "fingerprint": "fa3f2311cc4656147310dd129568d084c5431ff92c93d8750a0153c36165aa36",
  "inputs": {
    "OV-BR-05": {
      "locked_fingerprint": "c33a1ad86ab13ca03f4d06f63eff8971d4f1dcccb0870f3b5cba44fbe5527fbb",
      "path": "formal/markdown/locks/observables/OV-BR-05_bragg_lowk_slope_summary_OVERRIDE.md",
      "present": true,
      "record_fingerprint": "c33a1ad86ab13ca03f4d06f63eff8971d4f1dcccb0870f3b5cba44fbe5527fbb",
      "schema": "OV-BR-05_bragg_lowk_slope_summary/v1"
    },
    "OV-DR-BR-00": {
      "locked_fingerprint": "8a8ac0bbb690f6536dca4435e1014594d3ad20023e4c11e940002eefbe813dc0",
      "path": "formal/markdown/locks/observables/OV-DR-BR-00_br01_prediction_declarations_OVERRIDE.md",
      "present": true,
      "record_fingerprint": "8a8ac0bbb690f6536dca4435e1014594d3ad20023e4c11e940002eefbe813dc0",
      "schema": "OV-DR-BR-00_br01_prediction_declarations/v1"
    }
  },
  "observable_id": "OV-DR-BR-01",
  "rows": [
    {
      "candidate_id": "BR01_metric_from_DR01_fit_constant_density",
      "reason_codes": [
        "declared_br05_structure_satisfied"
      ],
      "survives_br01_constraints": "true"
    },
    {
      "candidate_id": "BR01_metric_from_DR01_fit_rest_frame_u0",
      "reason_codes": [
        "no_formal_br05_prediction_declared"
      ],
      "survives_br01_constraints": "unknown"
    },
    {
      "candidate_id": "BR01_metric_from_DR01_fit_unit_density",
      "reason_codes": [
        "declared_br05_structure_satisfied"
      ],
      "survives_br01_constraints": "true"
    },
    {
      "candidate_id": "BR01_metric_from_DR01_fit_unit_density_structural_fail",
      "reason_codes": [
        "missing_required_br05_fields",
        "missing_fields:condition_A:__REQUIRED_FIELD_THAT_DOES_NOT_EXIST__,condition_B:__REQUIRED_FIELD_THAT_DOES_NOT_EXIST__"
      ],
      "survives_br01_constraints": "false"
    }
  ],
  "schema": "OV-DR-BR-01_candidate_pruning_table/v1",
  "scope_limits": [
    "summary_only",
    "eliminative_only",
    "no_numeric_interpretation",
    "no_new_claims",
    "unknown_is_not_fail",
    "structural_pruning_even_if_blocked"
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
  },
  "summary": {
    "candidates": {
      "false": [
        "BR01_metric_from_DR01_fit_unit_density_structural_fail"
      ],
      "true": [
        "BR01_metric_from_DR01_fit_constant_density",
        "BR01_metric_from_DR01_fit_unit_density"
      ],
      "unknown": [
        "BR01_metric_from_DR01_fit_rest_frame_u0"
      ]
    },
    "counts": {
      "false": 1,
      "true": 2,
      "unknown": 1
    }
  }
}
```

Record fingerprint: `fa3f2311cc4656147310dd129568d084c5431ff92c93d8750a0153c36165aa36`
