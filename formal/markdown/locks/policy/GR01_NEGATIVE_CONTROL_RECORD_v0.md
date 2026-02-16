# GR01 Negative-Control Record v0

Record ID:
- `GR01_NEGATIVE_CONTROL_RECORD_v0`

Classification:
- `P-POLICY`

Purpose:
- Pin Phase III hard-negative controls for GR01 to verify predictable failure behavior.
- Prevent silent acceptance of physically or structurally invalid configurations.

Scope boundary:
- bounded/discrete weak-field v0 only
- no continuum-limit promotion
- no full-GR claim

Status token:
- `GR01_NEGATIVE_CONTROL_STATUS_v0: TEMPLATE_PINNED`
- `GR01_NEGATIVE_CONTROL_PROGRESS_v0: ROW_NEGCTRL_WRONG_KAPPA_SIGN_POPULATED`
- `GR01_NEGATIVE_CONTROL_PROGRESS_v0: ROW_NEGCTRL_BROKEN_SCALING_HIERARCHY_POPULATED`
- `GR01_NEGATIVE_CONTROL_PROGRESS_v0: ROW_NEGCTRL_BROKEN_WEAK_FIELD_BOUND_POPULATED`
- `GR01_NEGATIVE_CONTROL_PROGRESS_v0: ROW_NEGCTRL_BROKEN_SYMMETRY_OBLIGATION_POPULATED`
- `GR01_NEGATIVE_CONTROL_PROGRESS_v0: ROW_NEGCTRL_INCOMPATIBLE_CARRIERS_POPULATED`
- `GR01_NEGATIVE_CONTROL_PROGRESS_v0: ALL_REQUIRED_NEGATIVE_ROWS_POPULATED`

## Required negative controls (must remain present)

- `NEGCTRL_WRONG_KAPPA_SIGN_v0`
- `NEGCTRL_BROKEN_SCALING_HIERARCHY_v0`
- `NEGCTRL_BROKEN_WEAK_FIELD_BOUND_v0`
- `NEGCTRL_BROKEN_SYMMETRY_OBLIGATION_v0`
- `NEGCTRL_INCOMPATIBLE_CARRIERS_v0`

## Failure-mode contract (must remain present)

For each negative control:
- expected outcome must be explicit failure
- failure must include deterministic reason code and failing contract token
- no silent pass allowed

## Execution schema (template rows)

| Negative ID | Injected violation | Expected failure token | Observed failure token | Reason code | Artifact pointer |
|---|---|---|---|---|---|
| `NEGCTRL_WRONG_KAPPA_SIGN_v0` | `kappa_sign=flipped; regime_guard=unchanged` | `ELImpliesOperatorResidualUnderBound` | `ELImpliesOperatorResidualUnderBound` | `FAIL_WRONG_KAPPA_SIGN_BREAKS_OPERATOR_RESIDUAL_CONTRACT_v0` | `formal/output/gr01_negative_control_wrong_kappa_sign_v0.json` |
| `NEGCTRL_BROKEN_SCALING_HIERARCHY_v0` | `phi_scale_dominance=violated; rho_scale_dominance=violated; regime_guard=unchanged` | `WeakFieldScalingHierarchy` | `WeakFieldScalingHierarchy` | `FAIL_BROKEN_SCALING_HIERARCHY_BREAKS_TRUNCATION_ROUTE_v0` | `formal/output/gr01_negative_control_broken_scaling_hierarchy_v0.json` |
| `NEGCTRL_BROKEN_WEAK_FIELD_BOUND_v0` | `weak_field_uniform_bound=violated; bound_violation_magnitude=0.05; regime_guard=unchanged` | `WeakFieldUniformBound` | `WeakFieldUniformBound` | `FAIL_BROKEN_WEAK_FIELD_BOUND_BREAKS_REGIME_PREDICATE_ROUTE_v0` | `formal/output/gr01_negative_control_broken_weak_field_bound_v0.json` |
| `NEGCTRL_BROKEN_SYMMETRY_OBLIGATION_v0` | `projection_map_well_formed=violated; carrier_witness_consistency=violated; regime_guard=unchanged` | `ProjectionMapWellFormed` | `ProjectionMapWellFormed` | `FAIL_BROKEN_SYMMETRY_OBLIGATION_BREAKS_PROJECTION_WELL_FORMED_ROUTE_v0` | `formal/output/gr01_negative_control_broken_symmetry_obligation_v0.json` |
| `NEGCTRL_INCOMPATIBLE_CARRIERS_v0` | `carrier_pairing=incompatible; witness_consistency=violated; regime_guard=unchanged` | `ProjectionCarrierWitness` | `ProjectionCarrierWitness` | `FAIL_INCOMPATIBLE_CARRIERS_BREAK_PROJECTION_WITNESS_CONSISTENCY_v0` | `formal/output/gr01_negative_control_incompatible_carriers_v0.json` |

## Synchronization pointers

- Hardening target: `formal/docs/paper/DERIVATION_TARGET_GR01_HARDENING_v0.md`
- State checkpoint: `State_of_the_Theory.md`
