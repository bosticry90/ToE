# OV-DR-BR-00 — BR-01 prediction declarations (structural)

Scope / limits
- Structural-only declaration surface; no physics claim
- Hash-tracks the declaration source file
- Blocked-by-default if source missing

Record (computed)

```json
{
  "date": "2026-01-25",
  "fingerprint": "3dbe69bacb56466ed25f1bf5b3c332c7939550c4beb0027b7d3eb342b97f6690",
  "inputs": {
    "declarations": {
      "expected_path": "formal/python/toe/bridges/br01_prediction_declarations.json",
      "extra_candidate_ids": [],
      "path": "formal/python/toe/bridges/br01_prediction_declarations.json",
      "present": true,
      "raw_sha256": "eb39789ec5ecb386b898c96531037363915490857f0726946d5234e4d4a502f2",
      "schema": "BR01_prediction_declarations/v1",
      "version": 1
    }
  },
  "observable_id": "OV-DR-BR-00",
  "rows": [
    {
      "candidate_id": "BR01_metric_from_DR01_fit_constant_density",
      "declared": true,
      "prediction": {
        "kind": "br05_structure_required",
        "notes": [
          "Structural-only declaration: constant-density gauge candidate.",
          "No numeric constraints are declared here."
        ],
        "required_condition_keys": [
          "condition_A",
          "condition_B"
        ],
        "required_fields": [
          "c_mm_per_s",
          "se_mm_per_s"
        ]
      },
      "prediction_kind": "br05_structure_required"
    },
    {
      "candidate_id": "BR01_metric_from_DR01_fit_rest_frame_u0",
      "declared": false,
      "prediction": {},
      "prediction_kind": null
    },
    {
      "candidate_id": "BR01_metric_from_DR01_fit_unit_density",
      "declared": true,
      "prediction": {
        "kind": "br05_structure_required",
        "notes": [
          "Minimal structural declaration only: candidate is considered comparable if OV-BR-05 provides the declared condition keys and fields.",
          "No numeric constraints are declared here."
        ],
        "required_condition_keys": [
          "condition_A",
          "condition_B"
        ],
        "required_fields": [
          "c_mm_per_s",
          "se_mm_per_s"
        ]
      },
      "prediction_kind": "br05_structure_required"
    },
    {
      "candidate_id": "BR01_metric_from_DR01_fit_unit_density_structural_fail",
      "declared": true,
      "prediction": {
        "kind": "br05_structure_required",
        "notes": [
          "Intentionally failing structural declaration: includes an impossible required field key.",
          "This is a discriminative proof-of-pruning only (structural-only; no numeric constraints)."
        ],
        "required_condition_keys": [
          "condition_A",
          "condition_B"
        ],
        "required_fields": [
          "c_mm_per_s",
          "se_mm_per_s",
          "__REQUIRED_FIELD_THAT_DOES_NOT_EXIST__"
        ]
      },
      "prediction_kind": "br05_structure_required"
    }
  ],
  "schema": "OV-DR-BR-00_br01_prediction_declarations/v1",
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
      "sha256": "bf44287823ccbff8dc66260fb95611e5c44f4b8076d33a6d6e2072dc95be1a19",
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

Record fingerprint: `3dbe69bacb56466ed25f1bf5b3c332c7939550c4beb0027b7d3eb342b97f6690`
