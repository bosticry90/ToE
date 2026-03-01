# Derivation Target: Cosmology Background Micro-06 State-Checkpoint-Boundary v0

Spec ID:
- `DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_06_STATE_CHECKPOINT_BOUNDARY_v0`

Target ID:
- `TARGET-COSMO-BG-MICRO-06-STATE-CHECKPOINT-BOUNDARY-v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze Cycle-006 state-checkpoint boundary isolation for the COSMO rollup block.
- Keep COSMO rollup checkpoint tokens scoped to a bounded section in state.
- Prevent unrelated lane token bleed into COSMO checkpoint enforcement scope.

Adjudication token:
- `COSMO_BG_MICRO06_STATE_CHECKPOINT_ADJUDICATION: NOT_YET_DISCHARGED`

Scope-boundary token:
- `COSMO_BG_MICRO06_SCOPE_BOUNDARY_v0: COSMO_ROLLUP_STATE_CHECKPOINT_SECTION_ONLY_NONCLAIM`

Progress token:
- `COSMO_BG_MICRO06_PROGRESS_v0: STATE_CHECKPOINT_BOUNDARY_TOKEN_PINNED`

Artifact token:
- `COSMO_BG_MICRO06_STATE_CHECKPOINT_ARTIFACT_v0: cosmo_bg_micro06_state_checkpoint_boundary_cycle01_v0`

## TARGET section

- COSMO state-checkpoint boundary token:
  - `COSMO_ROLLUP_STATE_CHECKPOINT_BOUNDARY_v0: SECTION_ISOLATED`
- COSMO state-checkpoint end token:
  - `COSMO_ROLLUP_STATE_CHECKPOINT_END_v0`

## REQUIRED_COSMO_CHECKPOINT_CONTENTS section

- `formal/docs/paper/TOE_COSMO_BACKGROUND_PILLAR_SUMMARY_v0.md`
- `formal/markdown/locks/policy/COSMO_BACKGROUND_PILLAR_PACKAGE_v0.md`
- `COSMO_BACKGROUND_PILLAR_PACKAGE_STATUS_v0: FROZEN_CONTENTS_PINNED`
- `COSMO_BACKGROUND_PILLAR_PACKAGE_PROGRESS_v0: REQUIRED_CONTENTS_PINNED`
- `COSMO_BACKGROUND_REOPEN_POLICY_v0: FROZEN_WATCH_REOPEN_ON_REGRESSION`
- `formal/python/tests/test_cosmo_background_pillar_package_rollup_gate.py`
- `formal/python/tests/test_cosmo_state_rollup_checkpoint_gate.py`

## CANONICAL_ROUTE section

- Parent target pointer:
  - `formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md`
- State surface pointer:
  - `State_of_the_Theory.md`

## BOUNDED_SCOPE section

- COSMO rollup state-checkpoint section isolation only.
- no cosmology closure promotion.
- no derivation-grade claim.
- no comparator-lane authorization.
- no external truth claim.

## ADJUDICATION_SYNC section

- Cycle-006 micro adjudication token:
  - `COSMO_BG_MICRO06_STATE_CHECKPOINT_ADJUDICATION: NOT_YET_DISCHARGED`
- Cycle-006 micro progress token:
  - `COSMO_BG_MICRO06_PROGRESS_v0: STATE_CHECKPOINT_BOUNDARY_TOKEN_PINNED`
- Cycle-006 artifact pointer:
  - `formal/output/cosmo_bg_micro06_state_checkpoint_boundary_cycle01_v0.json`

Deliverable pointers:
- `formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md`
- `formal/output/cosmo_bg_micro06_state_checkpoint_boundary_cycle01_v0.json`
- `formal/python/tests/test_cosmo_bg_micro06_state_checkpoint_boundary_gate.py`
