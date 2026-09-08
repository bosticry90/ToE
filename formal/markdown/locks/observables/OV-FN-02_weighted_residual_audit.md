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
  "fingerprint": "074e8f0847d5d2c1ae2bb52fe56bb37b1fd760f4944f54d9e9c363fdd2be16bc",
  "inputs": {
    "FN-01_cross_fit_metric_residual_DR02_DR03": {
      "path": "formal/markdown/locks/functionals/FN-01_cross_fit_metric_residual_DR02_DR03.md",
      "present": true,
      "r_metric": 0.07422899055678828,
      "sha256": "b79f3ed5f2a1e290535d1b7736ff22a8a37c26e7d77c29de13ed616485eea2db"
    },
    "OV-FN-WT-02": {
      "locked_fingerprint": "80302fc58bcfe5d93741a823fe036a2bf7ef97f16e4b0ad4c02d38f0eb70855c",
      "path": "formal/markdown/locks/observables/OV-FN-WT-02_selected_weight_policy.md",
      "present": true,
      "record_fingerprint": "80302fc58bcfe5d93741a823fe036a2bf7ef97f16e4b0ad4c02d38f0eb70855c",
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
      "sha256": "bf44287823ccbff8dc66260fb95611e5c44f4b8076d33a6d6e2072dc95be1a19",
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

Record fingerprint: `074e8f0847d5d2c1ae2bb52fe56bb37b1fd760f4944f54d9e9c363fdd2be16bc`
