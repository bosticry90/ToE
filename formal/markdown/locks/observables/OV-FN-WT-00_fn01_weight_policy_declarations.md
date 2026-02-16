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
  "fingerprint": "cd98159ae2f8487475c8e5b43b9f0cb6ff7e9219b22c5bdb1fdee59dfab44af4",
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
    "no_new_claims",
    "blocked_by_admissibility_manifest",
    "requires_CT01_SYM01_CAUS01"
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
      "gate_disabled:CAUS01"
    ],
    "required_gates": [
      "CT01",
      "SYM01",
      "CAUS01"
    ]
  }
}
```

Record fingerprint: `cd98159ae2f8487475c8e5b43b9f0cb6ff7e9219b22c5bdb1fdee59dfab44af4`
