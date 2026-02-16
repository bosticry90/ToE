# OV-FN-WT-02 - Selected FN weight policy (computed)

Scope / limits
- Selection-only bookkeeping; no physics claim
- Deterministic; computed only from existing locks

Record (computed)

```json
{
  "date": "2026-01-25",
  "fingerprint": "07108d0610f0108d6600436d958904dc33171fb15df87c0d41f58251e3505710",
  "inputs": {
    "OV-FN-WT-01": {
      "locked_fingerprint": "b15b1c5b5671abd36ca0f38b00f70fdfec15d58c75b903ecb659bc39e4d580d6",
      "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\markdown\\locks\\observables\\OV-FN-WT-01_fn01_weight_policy_pruning_table.md",
      "present": true,
      "record_fingerprint": "b15b1c5b5671abd36ca0f38b00f70fdfec15d58c75b903ecb659bc39e4d580d6",
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
      "sha256": "284e1894ea9df1330bfd48c206b76af6e595a872996f2d5fed97b07cd3f0cce3",
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

Record fingerprint: `07108d0610f0108d6600436d958904dc33171fb15df87c0d41f58251e3505710`
