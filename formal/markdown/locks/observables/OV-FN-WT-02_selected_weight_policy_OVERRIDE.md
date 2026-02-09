# OV-FN-WT-02 - Selected FN weight policy (computed)

Scope / limits
- Selection-only bookkeeping; no physics claim
- Deterministic; computed only from existing locks

Record (computed)

```json
{
  "date": "2026-01-25",
  "fingerprint": "8cc81ee1864625af421a5f632f4311d49c38e81ac0432edc7032bb32a7d67a16",
  "inputs": {
    "OV-FN-WT-01": {
      "locked_fingerprint": "edcf08aa416b68811b86f7399ca57f663eb6d07c3d88207a951b24c048f90d0d",
      "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\markdown\\locks\\observables\\OV-FN-WT-01_fn01_weight_policy_pruning_table_OVERRIDE.md",
      "present": true,
      "record_fingerprint": "edcf08aa416b68811b86f7399ca57f663eb6d07c3d88207a951b24c048f90d0d",
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
    "computed_under_blocked_admissibility": false,
    "reason_codes": [
      "unique_survivor_selected"
    ],
    "selected_policy_id": "fnwt01_policy_loose",
    "selected_row": {
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
    "surviving_policy_ids": [
      "fnwt01_policy_loose"
    ]
  },
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

Record fingerprint: `8cc81ee1864625af421a5f632f4311d49c38e81ac0432edc7032bb32a7d67a16`
