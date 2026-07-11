# OV-FN-WT-02 - Selected FN weight policy (computed)

Scope / limits
- Selection-only bookkeeping; no physics claim
- Deterministic; computed only from existing locks

Record (computed)

```json
{
  "date": "2026-01-25",
  "fingerprint": "80302fc58bcfe5d93741a823fe036a2bf7ef97f16e4b0ad4c02d38f0eb70855c",
  "inputs": {
    "OV-FN-WT-01": {
      "locked_fingerprint": "cb2b6e7a99db7eb1cffaf5340466a2e63816eb52287fa93ae276851a657e3f6b",
      "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\markdown\\locks\\observables\\OV-FN-WT-01_fn01_weight_policy_pruning_table.md",
      "present": true,
      "record_fingerprint": "cb2b6e7a99db7eb1cffaf5340466a2e63816eb52287fa93ae276851a657e3f6b",
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
      "sha256": "bf44287823ccbff8dc66260fb95611e5c44f4b8076d33a6d6e2072dc95be1a19",
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

Record fingerprint: `80302fc58bcfe5d93741a823fe036a2bf7ef97f16e4b0ad4c02d38f0eb70855c`
