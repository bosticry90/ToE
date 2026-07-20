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
  "fingerprint": "a3d2f267d9c904f23f9aa01357f8a50997a3e304004291186260f35a9194a512",
  "inputs": {
    "OV-BR-05": {
      "locked_fingerprint": "428edbd0b97f696165ac0540d6888185e87410d575d9a1b6791b0def345286f8",
      "path": "formal/markdown/locks/observables/OV-BR-05_bragg_lowk_slope_summary.md",
      "present": true,
      "record_fingerprint": "428edbd0b97f696165ac0540d6888185e87410d575d9a1b6791b0def345286f8",
      "schema": "OV-BR-05_bragg_lowk_slope_summary/v1"
    },
    "OV-DR-BR-00": {
      "locked_fingerprint": "3dbe69bacb56466ed25f1bf5b3c332c7939550c4beb0027b7d3eb342b97f6690",
      "path": "formal/markdown/locks/observables/OV-DR-BR-00_br01_prediction_declarations.md",
      "present": true,
      "record_fingerprint": "3dbe69bacb56466ed25f1bf5b3c332c7939550c4beb0027b7d3eb342b97f6690",
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
      "path": "formal/markdown locks/gates/admissibility_manifest.json",
      "sha256": "bf44287823ccbff8dc66260fb95611e5c44f4b8076d33a6d6e2072dc95be1a19",
      "version": 1
    },
    "blocked": true,
    "reasons": [
      "gate_disabled:CT01",
      "gate_disabled:SYM01",
      "gate_disabled:CAUS01",
      "input_OV-BR-05_is_blocked",
      "input_OV-DR-BR-00_is_blocked"
    ],
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

Record fingerprint: `a3d2f267d9c904f23f9aa01357f8a50997a3e304004291186260f35a9194a512`
