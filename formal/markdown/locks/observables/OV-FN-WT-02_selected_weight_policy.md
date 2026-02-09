# OV-FN-WT-02 - Selected FN weight policy (computed)

Scope / limits
- Selection-only bookkeeping; no physics claim
- Deterministic; computed only from existing locks

Record (computed)

```json
{
  "date": "2026-01-25",
  "fingerprint": "85046d29824491c5c41a696bdd87eba7ef47e8b058100530b3bece5582b2fe17",
  "inputs": {
    "OV-FN-WT-01": {
      "locked_fingerprint": "c72f41b93249888ca6cf4216611527c0e35a709ae253d5805f59da36e5748f5b",
      "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\markdown\\locks\\observables\\OV-FN-WT-01_fn01_weight_policy_pruning_table.md",
      "present": true,
      "record_fingerprint": "c72f41b93249888ca6cf4216611527c0e35a709ae253d5805f59da36e5748f5b",
      "schema": "OV-FN-WT-01_fn01_weight_policy_pruning_table/v1"
    }
  },
  "observable_id": "OV-FN-WT-02",
  "schema": "OV-FN-WT-02_selected_weight_policy/v1",
  "scope_limits": [
    "selection_only",
    "lock_derived",
    "no_new_claims"
  ],
  "selection": {
    "computed_under_blocked_admissibility": true,
    "reason_codes": [
      "unique_survivor_selected",
      "computed_under_blocked_admissibility"
    ],
    "selected_policy_id": "fnwt01_policy_loose",
    "selected_row": {
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
    "surviving_policy_ids": [
      "fnwt01_policy_loose"
    ]
  },
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
      "input_OV-FN-WT-01_is_blocked"
    ],
    "required_gates": [
      "CT01",
      "SYM01",
      "CAUS01"
    ]
  }
}
```

Record fingerprint: `85046d29824491c5c41a696bdd87eba7ef47e8b058100530b3bece5582b2fe17`
