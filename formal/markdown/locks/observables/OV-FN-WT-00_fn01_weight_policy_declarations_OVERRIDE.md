# OV-FN-WT-00 — FN-01 weight policy declarations (structural)

Scope / limits
- Structural-only declaration surface; no physics claim
- Hash-tracks the declaration source file
- Blocked-by-default if source missing

Notes
- `br_candidate_id` is optional; when omitted it is treated as wildcard `"*"` (apply to all BR candidates)
- Wildcard semantics are deterministic and intended

Record (computed)

```json
{
  "date": "2026-01-25",
  "fingerprint": "7560b9697f58c2c6c384d19ad1a07e69b4424f81fa8d786eb3fb14a71c75a567",
  "inputs": {
    "declarations": {
      "expected_path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\python\\toe\\bridges\\fnwt01_weight_policy_declarations.json",
      "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\python\\toe\\bridges\\fnwt01_weight_policy_declarations.json",
      "present": true,
      "raw_sha256": "6991ce7aacdb0221b5e8846003a42817640523db7d96f0a23b43df6bdeeee32e",
      "schema": "FNWT01_weight_policy_declarations/v1",
      "unknown_br_candidate_ids": [],
      "unknown_fn_candidate_ids": [],
      "version": 1
    }
  },
  "observable_id": "OV-FN-WT-00",
  "rows": [
    {
      "br_candidate_id": "BR01_metric_from_DR01_fit_unit_density",
      "br_candidate_id_recognized": true,
      "fn_candidate_id": "fn01_make_P_cubic_artifact",
      "fn_candidate_id_recognized": true,
      "max_score": 0.08,
      "policy_id": "fnwt01_policy_loose",
      "w_fn": 1.0
    },
    {
      "br_candidate_id": "BR01_metric_from_DR01_fit_unit_density_structural_fail",
      "br_candidate_id_recognized": true,
      "fn_candidate_id": "fn01_make_P_cubic_artifact",
      "fn_candidate_id_recognized": true,
      "max_score": 0.05,
      "policy_id": "fnwt01_policy_strict",
      "w_fn": 1.0
    }
  ],
  "schema": "OV-FN-WT-00_fn01_weight_policy_declarations/v1",
  "scope_limits": [
    "structural_only",
    "hash_tracked_declaration_source",
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

Record fingerprint: `7560b9697f58c2c6c384d19ad1a07e69b4424f81fa8d786eb3fb14a71c75a567`
