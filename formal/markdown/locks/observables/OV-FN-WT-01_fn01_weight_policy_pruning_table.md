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
  "fingerprint": "7d44ea19066352fdf1afacb1a79a84f275cc881cd3aaea4b2cc05025265eb766",
  "inputs": {
    "FN-01_cross_fit_metric_residual_DR02_DR03": {
      "path": "formal/markdown/locks/functionals/FN-01_cross_fit_metric_residual_DR02_DR03.md",
      "present": true,
      "r_metric": 0.07422899055678828,
      "sha256": "b79f3ed5f2a1e290535d1b7736ff22a8a37c26e7d77c29de13ed616485eea2db"
    },
    "OV-BR-FN-01": {
      "locked_fingerprint": "5b10166c072804f803d735bc75f0ad09a852feacd96f7a5af5bf143a11a6b282",
      "path": "formal/markdown/locks/observables/OV-BR-FN-01_fn01_metric_residual_pruning_table.md",
      "present": true,
      "record_fingerprint": "5b10166c072804f803d735bc75f0ad09a852feacd96f7a5af5bf143a11a6b282",
      "schema": "OV-BR-FN-01_fn01_metric_residual_pruning_table/v1",
      "surviving_fn_candidate_ids": [
        "fn01_make_P_cubic_artifact"
      ]
    },
    "OV-DR-BR-01": {
      "locked_fingerprint": "a3d2f267d9c904f23f9aa01357f8a50997a3e304004291186260f35a9194a512",
      "path": "formal/markdown/locks/observables/OV-DR-BR-01_candidate_pruning_table.md",
      "present": true,
      "record_fingerprint": "a3d2f267d9c904f23f9aa01357f8a50997a3e304004291186260f35a9194a512",
      "schema": "OV-DR-BR-01_candidate_pruning_table/v1",
      "surviving_br_candidate_ids": [
        "BR01_metric_from_DR01_fit_constant_density",
        "BR01_metric_from_DR01_fit_unit_density"
      ]
    },
    "OV-FN-WT-00": {
      "locked_fingerprint": "cb2cf59a7de8db8989c70ffa3a2f079292ef5f0ec192b56a55ed45c667a826bf",
      "path": "formal/markdown/locks/observables/OV-FN-WT-00_fn01_weight_policy_declarations.md",
      "present": true,
      "record_fingerprint": "cb2cf59a7de8db8989c70ffa3a2f079292ef5f0ec192b56a55ed45c667a826bf",
      "schema": "OV-FN-WT-00_fn01_weight_policy_declarations/v1"
    }
  },
  "observable_id": "OV-FN-WT-01",
  "rows": [
    {
      "br_candidate_id": "BR01_metric_from_DR01_fit_unit_density",
      "computed_under_blocked_admissibility": true,
      "fn_candidate_id": "fn01_make_P_cubic_artifact",
      "max_score": 0.08,
      "policy_id": "fnwt01_policy_loose",
      "r_metric": 0.07422899055678828,
      "reason_codes": [
        "score_within_declared_max",
        "computed_under_blocked_admissibility"
      ],
      "score": 0.07422899055678828,
      "survives_fn_weight_policy_constraints": "true",
      "w_fn": 1.0
    },
    {
      "br_candidate_id": "BR01_metric_from_DR01_fit_unit_density_structural_fail",
      "computed_under_blocked_admissibility": true,
      "fn_candidate_id": "fn01_make_P_cubic_artifact",
      "max_score": 0.05,
      "policy_id": "fnwt01_policy_strict",
      "r_metric": 0.07422899055678828,
      "reason_codes": [
        "br_candidate_failed_upstream_pruning",
        "computed_under_blocked_admissibility"
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
      "path": "formal/markdown locks/gates/admissibility_manifest.json",
      "sha256": "bf44287823ccbff8dc66260fb95611e5c44f4b8076d33a6d6e2072dc95be1a19",
      "version": 1
    },
    "blocked": true,
    "reasons": [
      "gate_disabled:CT01",
      "gate_disabled:SYM01",
      "gate_disabled:CAUS01",
      "input_OV-BR-FN-01_is_blocked",
      "input_OV-DR-BR-01_is_blocked",
      "input_OV-FN-WT-00_is_blocked"
    ],
    "required_gates": [
      "CT01",
      "SYM01",
      "CAUS01"
    ]
  }
}
```

Record fingerprint: `7d44ea19066352fdf1afacb1a79a84f275cc881cd3aaea4b2cc05025265eb766`
