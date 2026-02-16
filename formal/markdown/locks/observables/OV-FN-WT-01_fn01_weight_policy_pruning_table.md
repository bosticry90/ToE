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
  "fingerprint": "b15b1c5b5671abd36ca0f38b00f70fdfec15d58c75b903ecb659bc39e4d580d6",
  "inputs": {
    "FN-01_cross_fit_metric_residual_DR02_DR03": {
      "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\markdown\\locks\\functionals\\FN-01_cross_fit_metric_residual_DR02_DR03.md",
      "present": true,
      "r_metric": 0.07422899055678828,
      "sha256": "b79f3ed5f2a1e290535d1b7736ff22a8a37c26e7d77c29de13ed616485eea2db"
    },
    "OV-BR-FN-01": {
      "locked_fingerprint": "c9d3c4122693e9f0f4dbbc30c3040a527750b638e46945c8f32aba08135ed97b",
      "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\markdown\\locks\\observables\\OV-BR-FN-01_fn01_metric_residual_pruning_table.md",
      "present": true,
      "record_fingerprint": "c9d3c4122693e9f0f4dbbc30c3040a527750b638e46945c8f32aba08135ed97b",
      "schema": "OV-BR-FN-01_fn01_metric_residual_pruning_table/v1",
      "surviving_fn_candidate_ids": [
        "fn01_make_P_cubic_artifact"
      ]
    },
    "OV-DR-BR-01": {
      "locked_fingerprint": "89065261befb4c400eae8a861d73d0cd655cb70099aa1f4c8031ce6c7e8982db",
      "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\markdown\\locks\\observables\\OV-DR-BR-01_candidate_pruning_table.md",
      "present": true,
      "record_fingerprint": "89065261befb4c400eae8a861d73d0cd655cb70099aa1f4c8031ce6c7e8982db",
      "schema": "OV-DR-BR-01_candidate_pruning_table/v1",
      "surviving_br_candidate_ids": [
        "BR01_metric_from_DR01_fit_constant_density",
        "BR01_metric_from_DR01_fit_unit_density"
      ]
    },
    "OV-FN-WT-00": {
      "locked_fingerprint": "cd98159ae2f8487475c8e5b43b9f0cb6ff7e9219b22c5bdb1fdee59dfab44af4",
      "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\markdown\\locks\\observables\\OV-FN-WT-00_fn01_weight_policy_declarations.md",
      "present": true,
      "record_fingerprint": "cd98159ae2f8487475c8e5b43b9f0cb6ff7e9219b22c5bdb1fdee59dfab44af4",
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
      "sha256": "284e1894ea9df1330bfd48c206b76af6e595a872996f2d5fed97b07cd3f0cce3",
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

Record fingerprint: `b15b1c5b5671abd36ca0f38b00f70fdfec15d58c75b903ecb659bc39e4d580d6`
