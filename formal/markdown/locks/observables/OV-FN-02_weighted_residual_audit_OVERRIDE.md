# OV-FN-02 - Weighted residual audit (computed)

Scope / limits
- Audit-only bookkeeping; no physics claim
- Applies declared weights to a locked scalar residual

Record (computed)

```json
{
  "audit": {
    "br_candidate_id": "BR01_metric_from_DR01_fit_unit_density",
    "computed_under_blocked_admissibility": false,
    "max_score": 0.08,
    "r_metric": 0.07422899055678828,
    "reason_codes": [
      "weighted_score_computed"
    ],
    "selected_policy_id": "fnwt01_policy_loose",
    "w_fn": 1.0,
    "weighted_score": 0.07422899055678828,
    "within_threshold": true
  },
  "date": "2026-01-25",
  "fingerprint": "708916328c682c66e7b5e7fd23a0555df57c910abb99b67e8d25c99643361a9a",
  "inputs": {
    "FN-01_cross_fit_metric_residual_DR02_DR03": {
      "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\markdown\\locks\\functionals\\FN-01_cross_fit_metric_residual_DR02_DR03.md",
      "present": true,
      "r_metric": 0.07422899055678828,
      "sha256": "b79f3ed5f2a1e290535d1b7736ff22a8a37c26e7d77c29de13ed616485eea2db"
    },
    "OV-FN-WT-02": {
      "locked_fingerprint": "8cc81ee1864625af421a5f632f4311d49c38e81ac0432edc7032bb32a7d67a16",
      "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\markdown\\locks\\observables\\OV-FN-WT-02_selected_weight_policy_OVERRIDE.md",
      "present": true,
      "record_fingerprint": "8cc81ee1864625af421a5f632f4311d49c38e81ac0432edc7032bb32a7d67a16",
      "schema": "OV-FN-WT-02_selected_weight_policy/v1"
    }
  },
  "observable_id": "OV-FN-02",
  "schema": "OV-FN-02_weighted_residual_audit/v1",
  "scope_limits": [
    "audit_only",
    "declared_weight_application_only",
    "lock_derived",
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

Record fingerprint: `708916328c682c66e7b5e7fd23a0555df57c910abb99b67e8d25c99643361a9a`
