# PTC NLSE v1 Front Door Surface Contract (bounded)

Last updated: 2026-02-08

## Purpose

Freeze the executable surface for `PTC-NLSE-v1` so it can be used as the reference substrate.
This is a governance and reproducibility contract only. It does not elevate physical truth claims.

## Canonical surface

- Runner: `formal/python/tools/ptc_nlse_v1_run.py`
- Manifest: `formal/quarantine/physics_target/PTC_NLSE_V1_MANIFEST.json`
- Locked report artifacts:
  - `formal/output/PTC_NLSE_V1_REPORT.json`
  - `formal/output/PTC_NLSE_V1_REPORT_DISSIPATIVE.json`
  - `formal/output/PTC_NLSE_V1_REPORT_SOLITON.json`
  - `formal/output/PTC_NLSE_V1_REPORT_SOLITON_DISSIPATIVE.json`
  - `formal/output/PTC_NLSE_V1_REPORT_TRAP.json`
  - `formal/output/PTC_NLSE_V1_REPORT_TRAP_DISSIPATIVE.json`
- Locked hooks artifacts:
  - `formal/output/PTC_NLSE_V1_HOOKS.json`
  - `formal/output/PTC_NLSE_V1_HOOKS_DISSIPATIVE.json`
  - `formal/output/PTC_NLSE_V1_HOOKS_SOLITON.json`
  - `formal/output/PTC_NLSE_V1_HOOKS_SOLITON_DISSIPATIVE.json`
  - `formal/output/PTC_NLSE_V1_HOOKS_TRAP.json`
  - `formal/output/PTC_NLSE_V1_HOOKS_TRAP_DISSIPATIVE.json`

## Schema ids (frozen at v1)

- Manifest schema: `PTC/NLSE_v1_manifest/v1`
- Report schema: `PTC/NLSE_v1_report/v1`
- Hooks schema: `PTC/NLSE_v1_hooks/v1`

## Input contract

Common required input fields:

- `regime`, `dimension`, `n`, `L`, `dt`, `steps`, `sample_every`
- `g`, `V0`, `gamma`, `A_re`, `A_im`, `k`, `phase`
- `case_id`

Optional trap fields (required only for harmonic trap cases):

- `V_kind` with value `harmonic`
- `V_trap_omega`
- `V_center`

## Report contract

Top-level keys are frozen:

- `schema`, `inputs`, `input_fingerprint`, `derived`, `output`, `determinism`, `fingerprint`

Derived keys:

- Base lanes: `grid`, `kgrid_sample`, `rac_energy_class`
- Soliton lanes: base keys plus `initial_condition=sech_soliton`
- Trap lanes: base keys plus `initial_condition=harmonic_ground_state_like`, `potential`

Output keys:

- Core keys (all report lanes):
  - `omega_hat`, `omega_expected`, `omega_error`
  - `energy_trace`, `norm_trace`, `energy_delta`, `norm_delta`
  - `phase_invariance_error`, `time_reversal_error`, `t_end`
- Soliton extensions:
  - `shape_residual`, `shape_peak_delta`, `shape_peak_ratio`
- Trap extensions:
  - `trap_shape_residual`, `trap_peak_ratio`, `trap_m2_delta`

## Hooks contract

Top-level keys are frozen:

- `schema`, `inputs`, `input_fingerprint`, `hooks`, `determinism`, `fingerprint`

Hooks keys are frozen:

- `sym01_phase_residual`
- `sym01_conjugation_residual`
- `par01_parity_residual`
- `par01_advection_break_residual`
- `bc01_boundary_residual`
- `bc01_periodic_constant_residual`
- `bc01_dirichlet_constant_residual`

## Determinism and freeze policy

- Locked artifacts are deterministic at fixed inputs.
- Any schema or required-key change requires a new schema version and explicit migration/lock update.
- v1 remains stable while v2 development happens on a separate lane.

## Test evidence

- Determinism locks: `formal/python/tests/test_ptc_nlse_v1_front_door_determinism.py`
- Surface contract freeze: `formal/python/tests/test_ptc_nlse_v1_surface_contract_freeze.py`
- Lane semantics: `formal/python/tests/test_en01_energy_monotonicity_lane.py`, `formal/python/tests/test_st01_soliton_shape_preservation_lane.py`, `formal/python/tests/test_st01_soliton_resolution_convergence_lane.py`, `formal/python/tests/test_tg01_trapped_ground_state_lane.py`
