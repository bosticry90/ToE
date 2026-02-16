# OV-CV-BR-01 - CV01 v1 -> pruning bridge (summary-only)

Scope / limits
- Summary-only / eliminative-only bookkeeping
- Explicit CV01 reason-code to reason-atom mapping only
- No implicit coupling with BR-only pruning lanes
- No numeric interpretation and no external truth claim

Record (computed)

```json
{
  "active_reason_atoms": [],
  "active_reason_codes": [
    "cv01_v1_cross_artifact_speed_consistent"
  ],
  "date": "2026-02-08",
  "fingerprint": "55fda51ed3f5ef7af784fbab9221a27ff52c362b2235e99affc27eef5752dbc3",
  "inputs": {
    "OV-CV-01_v1": {
      "artifact_dir": "C:\\Users\\psboy\\Documents\\ToE\\formal\\external_evidence\\bec_bragg_steinhauer_2001",
      "record_fingerprint": "b56e3047654bda6bf93a9a7b11ad6d2166f79762c329c7a95dc3c3592f668ffe",
      "schema": "OV-CV-01_bec_bragg_v1_comparator/v1",
      "status_blocked": false
    },
    "OV-DR-BR-01": {
      "record_fingerprint": "89065261befb4c400eae8a861d73d0cd655cb70099aa1f4c8031ce6c7e8982db",
      "schema": "OV-DR-BR-01_candidate_pruning_table/v1",
      "status_blocked": true
    },
    "policy": {
      "path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\python\\toe\\observables\\cv01_v1_pruning_reason_policy.json",
      "present": true,
      "raw_sha256": "5ff4baf646434c387bfe4a559c1605a46c18c856e6cf2978c9a9b552245f2190",
      "schema": "OVCV01_v1_pruning_reason_policy/v1",
      "version": 1
    }
  },
  "mapping_policy": {
    "eliminative_atoms": [
      "cv01_cross_artifact_inconsistent",
      "cv01_invalid_speed_sign"
    ],
    "reason_code_to_atom": {
      "cv01_fail_cross_artifact_missing_inputs": "cv01_missing_inputs_blocked",
      "cv01_fail_cross_artifact_nonpositive_speed": "cv01_invalid_speed_sign",
      "cv01_fail_linear_vs_curved_speed_inconsistent": "cv01_cross_artifact_inconsistent"
    },
    "schema": "OVCV01_v1_pruning_reason_policy/v1",
    "version": 1
  },
  "observable_id": "OV-CV-BR-01",
  "rows": [
    {
      "base_survives_br01_constraints": "true",
      "candidate_id": "BR01_metric_from_DR01_fit_constant_density",
      "cv01_attributed_elimination": false,
      "cv01_reason_atoms_considered": [
        "cv01_cross_artifact_inconsistent"
      ],
      "cv01_reason_atoms_triggered": [],
      "reason_codes": [
        "declared_br05_structure_satisfied"
      ],
      "survives_cv01_bridge_constraints": "true"
    },
    {
      "base_survives_br01_constraints": "unknown",
      "candidate_id": "BR01_metric_from_DR01_fit_rest_frame_u0",
      "cv01_attributed_elimination": false,
      "cv01_reason_atoms_considered": [],
      "cv01_reason_atoms_triggered": [],
      "reason_codes": [
        "no_formal_br05_prediction_declared"
      ],
      "survives_cv01_bridge_constraints": "unknown"
    },
    {
      "base_survives_br01_constraints": "true",
      "candidate_id": "BR01_metric_from_DR01_fit_unit_density",
      "cv01_attributed_elimination": false,
      "cv01_reason_atoms_considered": [],
      "cv01_reason_atoms_triggered": [],
      "reason_codes": [
        "declared_br05_structure_satisfied"
      ],
      "survives_cv01_bridge_constraints": "true"
    },
    {
      "base_survives_br01_constraints": "false",
      "candidate_id": "BR01_metric_from_DR01_fit_unit_density_structural_fail",
      "cv01_attributed_elimination": false,
      "cv01_reason_atoms_considered": [
        "cv01_invalid_speed_sign"
      ],
      "cv01_reason_atoms_triggered": [],
      "reason_codes": [
        "missing_required_br05_fields",
        "missing_fields:condition_A:__REQUIRED_FIELD_THAT_DOES_NOT_EXIST__,condition_B:__REQUIRED_FIELD_THAT_DOES_NOT_EXIST__",
        "retained_base_pruning_elimination"
      ],
      "survives_cv01_bridge_constraints": "false"
    }
  ],
  "schema": "OV-CV-BR-01_cv01_v1_pruning_bridge/v1",
  "scope_limits": [
    "summary_only",
    "eliminative_only",
    "explicit_cv01_reason_atom_mapping",
    "no_implicit_coupling",
    "no_new_claims",
    "survivor_guard_required"
  ],
  "status": {
    "blocked": true,
    "cv01_tolerance_profile": "pinned",
    "reasons": [
      "base_pruning_status_blocked"
    ]
  },
  "summary": {
    "candidates": {
      "false": [
        "BR01_metric_from_DR01_fit_unit_density_structural_fail"
      ],
      "true": [
        "BR01_metric_from_DR01_fit_constant_density",
        "BR01_metric_from_DR01_fit_unit_density"
      ],
      "unknown": [
        "BR01_metric_from_DR01_fit_rest_frame_u0"
      ]
    },
    "counts": {
      "false": 1,
      "true": 2,
      "unknown": 1
    },
    "cv01_attributed_elimination_count": 0,
    "cv01_attributed_eliminations": [],
    "survivor_guard": true
  }
}
```

Record fingerprint: `55fda51ed3f5ef7af784fbab9221a27ff52c362b2235e99affc27eef5752dbc3`
