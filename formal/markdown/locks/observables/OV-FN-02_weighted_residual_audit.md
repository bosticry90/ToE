# OV-FN-02 - Weighted residual audit (computed)

Scope / limits
- Audit-only bookkeeping; no physics claim
- Applies declared weights to a locked scalar residual

Record (computed)

```json
{
  "audit": {
    "br_candidate_id": "BR01_metric_from_DR01_fit_unit_density",
    "computed_under_blocked_admissibility": true,
    "max_score": 0.08,
    "r_metric": 0.07422899055678828,
    "reason_codes": [
      "weighted_score_computed",
      "computed_under_blocked_admissibility"
    ],
    "selected_policy_id": "fnwt01_policy_loose",
    "w_fn": 1.0,
    "weighted_score": 0.07422899055678828,
    "within_threshold": true
  },
  "date": "2026-01-25",
  "fingerprint": "67fa4dfd3467d99e2195e83616d9c6aaed5deae3cd492df6a74e0e8481c7312f",
  "inputs": {
    "FN-01_cross_fit_metric_residual_DR02_DR03": {
      "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\markdown\\locks\\functionals\\FN-01_cross_fit_metric_residual_DR02_DR03.md",
      "present": true,
      "r_metric": 0.07422899055678828,
      "sha256": "b79f3ed5f2a1e290535d1b7736ff22a8a37c26e7d77c29de13ed616485eea2db"
    },
    "OV-FN-WT-02": {
      "locked_fingerprint": "85046d29824491c5c41a696bdd87eba7ef47e8b058100530b3bece5582b2fe17",
      "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\markdown\\locks\\observables\\OV-FN-WT-02_selected_weight_policy.md",
      "present": true,
      "record_fingerprint": "85046d29824491c5c41a696bdd87eba7ef47e8b058100530b3bece5582b2fe17",
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
      "path": "formal/markdown locks/gates/admissibility_manifest.json",
      "sha256": "99a290146c803db75d94be40c656db8f00afb59fd60d4d76b9640e8a3cbbc750",
      "version": 1
    },
    "blocked": true,
    "reasons": [
      "gate_disabled:CT01",
      "gate_disabled:SYM01",
      "gate_disabled:CAUS01",
      "input_OV-FN-WT-02_is_blocked"
    ],
    "required_gates": [
      "CT01",
      "SYM01",
      "CAUS01"
    ]
  }
}
```

Record fingerprint: `67fa4dfd3467d99e2195e83616d9c6aaed5deae3cd492df6a74e0e8481c7312f`
