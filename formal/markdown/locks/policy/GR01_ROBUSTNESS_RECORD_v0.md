# GR01 Robustness Record v0

Record ID:
- `GR01_ROBUSTNESS_RECORD_v0`

Classification:
- `P-POLICY`

Purpose:
- Pin Phase III perturbation-robustness obligations for GR01 inside bounded/discrete weak-field v0 scope.
- Ensure failures are informative and explicitly reason-coded.

Scope boundary:
- bounded/discrete weak-field v0 only
- no continuum-limit promotion
- no full-GR claim

Status token:
- `GR01_ROBUSTNESS_STATUS_v0: TEMPLATE_PINNED`
- `GR01_ROBUSTNESS_PROGRESS_v0: ROW_PERTURB_RHO_SMALL_POPULATED`
- `GR01_ROBUSTNESS_PROGRESS_v0: ROW_PERTURB_PHI_SMALL_POPULATED`
- `GR01_ROBUSTNESS_PROGRESS_v0: ROW_PERTURB_DISCRETIZATION_PARAMS_POPULATED`
- `GR01_ROBUSTNESS_PROGRESS_v0: ROW_PERTURB_BOUNDARY_HANDLING_POPULATED`
- `GR01_ROBUSTNESS_PROGRESS_v0: ROW_PERTURB_PROJECTION_CONDITIONS_POPULATED`
- `GR01_ROBUSTNESS_PROGRESS_v0: ALL_REQUIRED_PERTURBATION_ROWS_POPULATED`

## Required perturbation families (must remain present)

- `PERTURB_RHO_SMALL_v0`
- `PERTURB_PHI_SMALL_v0`
- `PERTURB_DISCRETIZATION_PARAMS_v0`
- `PERTURB_BOUNDARY_HANDLING_v0`
- `PERTURB_PROJECTION_CONDITIONS_v0`

## Outcome contract (must remain present)

For each perturbation family, record one of:
- `OUTCOME_STILL_DERIVES_POISSON_RESIDUAL`
- `OUTCOME_FAILS_INFORMATIVE`

If failure occurs, include:
- deterministic reason code
- first failing gate/theorem token
- minimal reproducer pointer

## Execution schema (template rows)

| Perturbation ID | Input delta | Expected outcome | Observed outcome | Reason code | Artifact pointer |
|---|---|---|---|---|---|
| `PERTURB_RHO_SMALL_v0` | `rho_multiplier=1.01; phi_perturbation=0.0; regime_guard=unchanged` | `OUTCOME_STILL_DERIVES_POISSON_RESIDUAL` | `OUTCOME_STILL_DERIVES_POISSON_RESIDUAL` | `PASS_RESIDUAL_STABLE_UNDER_SMALL_RHO_PERTURBATION_v0` | `formal/output/gr01_robustness_perturb_rho_small_v0.json` |
| `PERTURB_PHI_SMALL_v0` | `phi_multiplier=1.01; rho_perturbation=0.0; regime_guard=unchanged` | `OUTCOME_STILL_DERIVES_POISSON_RESIDUAL` | `OUTCOME_STILL_DERIVES_POISSON_RESIDUAL` | `PASS_RESIDUAL_STABLE_UNDER_SMALL_PHI_PERTURBATION_v0` | `formal/output/gr01_robustness_perturb_phi_small_v0.json` |
| `PERTURB_DISCRETIZATION_PARAMS_v0` | `epsilon_multiplier=1.01; fd_step_policy=default_binding_perturbed_small; regime_guard=unchanged` | `OUTCOME_STILL_DERIVES_POISSON_RESIDUAL` | `OUTCOME_STILL_DERIVES_POISSON_RESIDUAL` | `PASS_RESIDUAL_STABLE_UNDER_SMALL_DISCRETIZATION_PERTURBATION_v0` | `formal/output/gr01_robustness_perturb_discretization_params_v0.json` |
| `PERTURB_BOUNDARY_HANDLING_v0` | `boundary_policy_variant=periodic_edge_tolerance_small; boundary_delta=0.01; regime_guard=unchanged` | `OUTCOME_STILL_DERIVES_POISSON_RESIDUAL` | `OUTCOME_STILL_DERIVES_POISSON_RESIDUAL` | `PASS_RESIDUAL_STABLE_UNDER_SMALL_BOUNDARY_PERTURBATION_v0` | `formal/output/gr01_robustness_perturb_boundary_handling_v0.json` |
| `PERTURB_PROJECTION_CONDITIONS_v0` | `projection_condition_variant=well_formed_small_shift; carrier_alignment_tolerance=0.01; regime_guard=unchanged` | `OUTCOME_STILL_DERIVES_POISSON_RESIDUAL` | `OUTCOME_STILL_DERIVES_POISSON_RESIDUAL` | `PASS_RESIDUAL_STABLE_UNDER_SMALL_PROJECTION_CONDITION_PERTURBATION_v0` | `formal/output/gr01_robustness_perturb_projection_conditions_v0.json` |

## Synchronization pointers

- Hardening target: `formal/docs/paper/DERIVATION_TARGET_GR01_HARDENING_v0.md`
- State checkpoint: `State_of_the_Theory.md`
