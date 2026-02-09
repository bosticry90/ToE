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
    "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\python\\toe\\bridges\\br01_candidates.py"
  },
  "date": "2026-01-25",
  "fingerprint": "c302f9469e151d2c93d4837684c08fee4a64d648f9da648c37c509569dbb5d24",
  "inputs": {
    "OV-BR-05": {
      "locked_fingerprint": "093c40dcfc088f16b0b40b082c53aa6d9e7410f74294e256b1592861550675e1",
      "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\markdown\\locks\\observables\\OV-BR-05_bragg_lowk_slope_summary_OVERRIDE.md",
      "present": true,
      "record_fingerprint": "093c40dcfc088f16b0b40b082c53aa6d9e7410f74294e256b1592861550675e1",
      "schema": "OV-BR-05_bragg_lowk_slope_summary/v1"
    },
    "OV-DR-BR-00": {
      "locked_fingerprint": "9d9394f968554686f8c067fe4f696c8cbd15dcbb5228bf00f0874af63812d764",
      "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\markdown\\locks\\observables\\OV-DR-BR-00_br01_prediction_declarations_OVERRIDE.md",
      "present": true,
      "record_fingerprint": "9d9394f968554686f8c067fe4f696c8cbd15dcbb5228bf00f0874af63812d764",
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

Record fingerprint: `c302f9469e151d2c93d4837684c08fee4a64d648f9da648c37c509569dbb5d24`
