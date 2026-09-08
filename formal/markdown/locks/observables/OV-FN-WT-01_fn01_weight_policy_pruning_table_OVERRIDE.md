# OV-FN-WT-01 — Pruning table (FN-01 weight policies; summary-only)

Scope / limits
- Summary-only / eliminative-only bookkeeping
- Applies declared thresholds to a locked scalar (R_metric)
- Unknown is not fail

Notes
- If an upstream declaration uses `br_candidate_id = "*"`, WT-01 expands it over all BR candidates
- Expansion order is deterministic: BR candidate ids sorted lexicographically

Record (computed)

```json
{
  "date": "2026-01-25",
  "fingerprint": "a86cd0d18626f2e8715da72a37df325553fceb2831023fcc6a9f67360471be8c",
  "inputs": {
    "FN-01_cross_fit_metric_residual_DR02_DR03": {
      "path": "formal/markdown/locks/functionals/FN-01_cross_fit_metric_residual_DR02_DR03.md",
      "present": true,
      "r_metric": 0.07422899055678828,
      "sha256": "b79f3ed5f2a1e290535d1b7736ff22a8a37c26e7d77c29de13ed616485eea2db"
    },
    "OV-BR-FN-01": {
      "locked_fingerprint": "5bf01ad41550e3fe60b0d1b108dcc93c351f8cf70ab58d784138817d84e7aa40",
      "path": "formal/markdown/locks/observables/OV-BR-FN-01_fn01_metric_residual_pruning_table_OVERRIDE.md",
      "present": true,
      "record_fingerprint": "5bf01ad41550e3fe60b0d1b108dcc93c351f8cf70ab58d784138817d84e7aa40",
      "schema": "OV-BR-FN-01_fn01_metric_residual_pruning_table/v1",
      "surviving_fn_candidate_ids": [
        "fn01_make_P_cubic_artifact"
      ]
    },
    "OV-DR-BR-01": {
      "locked_fingerprint": "fa3f2311cc4656147310dd129568d084c5431ff92c93d8750a0153c36165aa36",
      "path": "formal/markdown/locks/observables/OV-DR-BR-01_candidate_pruning_table_OVERRIDE.md",
      "present": true,
      "record_fingerprint": "fa3f2311cc4656147310dd129568d084c5431ff92c93d8750a0153c36165aa36",
      "schema": "OV-DR-BR-01_candidate_pruning_table/v1",
      "surviving_br_candidate_ids": [
        "BR01_metric_from_DR01_fit_constant_density",
        "BR01_metric_from_DR01_fit_unit_density"
      ]
    },
    "OV-FN-WT-00": {
      "locked_fingerprint": "4dd40875ee396f12afac0c7e3577c0d057f5c5a96dfe598b85e674beb3de38d0",
      "path": "formal/markdown/locks/observables/OV-FN-WT-00_fn01_weight_policy_declarations_OVERRIDE.md",
      "present": true,
      "record_fingerprint": "4dd40875ee396f12afac0c7e3577c0d057f5c5a96dfe598b85e674beb3de38d0",
      "schema": "OV-FN-WT-00_fn01_weight_policy_declarations/v1"
    }
  },
  "observable_id": "OV-FN-WT-01",
  "rows": [
    {
      "br_candidate_id": "BR01_metric_from_DR01_fit_unit_density",
      "computed_under_blocked_admissibility": false,
      "fn_candidate_id": "fn01_make_P_cubic_artifact",
      "max_score": 0.08,
      "policy_id": "fnwt01_policy_loose",
      "r_metric": 0.07422899055678828,
      "reason_codes": [
        "score_within_declared_max"
      ],
      "score": 0.07422899055678828,
      "survives_fn_weight_policy_constraints": "true",
      "w_fn": 1.0
    },
    {
      "br_candidate_id": "BR01_metric_from_DR01_fit_unit_density_structural_fail",
      "computed_under_blocked_admissibility": false,
      "fn_candidate_id": "fn01_make_P_cubic_artifact",
      "max_score": 0.05,
      "policy_id": "fnwt01_policy_strict",
      "r_metric": 0.07422899055678828,
      "reason_codes": [
        "br_candidate_failed_upstream_pruning"
      ],
      "score": null,
      "survives_fn_weight_policy_constraints": "false",
      "w_fn": 1.0
    }
  ],
  "schema": "OV-FN-WT-01_fn01_weight_policy_pruning_table/v1",
  "scope_limits": [
    "summary_only",
    "eliminative_only",
    "unknown_is_not_fail",
    "declared_threshold_application_only",
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

Record fingerprint: `a86cd0d18626f2e8715da72a37df325553fceb2831023fcc6a9f67360471be8c`
