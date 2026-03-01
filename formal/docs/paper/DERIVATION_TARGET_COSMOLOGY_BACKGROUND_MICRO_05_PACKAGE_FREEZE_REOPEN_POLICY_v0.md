# Derivation Target: Cosmology Background Micro-05 Package-Freeze/Reopen-Policy v0

Spec ID:
- `DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_05_PACKAGE_FREEZE_REOPEN_POLICY_v0`

Target ID:
- `TARGET-COSMO-BG-MICRO-05-PACKAGE-FREEZE-REOPEN-POLICY-v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze Cycle-005 package-freeze and reopen-policy surfaces for the cosmology background lane.
- Pin reopen triggers and required package contents before any closure promotion.
- Keep the lane bounded, non-claim, and scaffold-only by construction.

Adjudication token:
- `COSMO_BG_MICRO05_PACKAGE_FREEZE_ADJUDICATION: NOT_YET_DISCHARGED`

Scope-boundary token:
- `COSMO_BG_MICRO05_SCOPE_BOUNDARY_v0: PACKAGE_FREEZE_REOPEN_POLICY_ONLY_NONCLAIM`

Progress token:
- `COSMO_BG_MICRO05_PROGRESS_v0: PACKAGE_FREEZE_REOPEN_POLICY_TOKEN_PINNED`

Artifact token:
- `COSMO_BG_MICRO05_PACKAGE_FREEZE_ARTIFACT_v0: cosmo_bg_micro05_package_freeze_reopen_policy_cycle01_v0`

## TARGET section

- Package-freeze status token:
  - `COSMO_BG_MICRO05_PACKAGE_FREEZE_STATUS_v0: FROZEN_CONTENTS_PINNED`
- Reopen-policy token:
  - `COSMO_BG_MICRO05_REOPEN_POLICY_v0: FROZEN_WATCH_REOPEN_ON_REGRESSION`
- Reopen trigger token (surface drift):
  - `COSMO_BG_MICRO05_REOPEN_TRIGGER_SURFACE_DRIFT_v0: ENABLED`
- Reopen trigger token (scope-boundary regression):
  - `COSMO_BG_MICRO05_REOPEN_TRIGGER_SCOPE_REGRESSION_v0: ENABLED`

## REQUIRED_PACKAGE_CONTENTS section

- `formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_01_OBJECT_SURFACE_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_02_EXPANSION_LAW_SURFACE_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_03_SOURCE_COUPLING_SURFACE_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_04_REGIME_FALSIFIABILITY_SURFACE_v0.md`

## CANONICAL_ROUTE section

- Parent target pointer:
  - `formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md`

## BOUNDED_SCOPE section

- package-freeze/reopen-policy scaffold scope only.
- no Einstein-equation closure claim.
- no Friedmann derivation closure claim.
- no perturbation-theory closure claim.
- no full cosmological model completion claim.
- no external truth claim.

## ADJUDICATION_SYNC section

- Cycle-005 micro adjudication token:
  - `COSMO_BG_MICRO05_PACKAGE_FREEZE_ADJUDICATION: NOT_YET_DISCHARGED`
- Cycle-005 micro progress token:
  - `COSMO_BG_MICRO05_PROGRESS_v0: PACKAGE_FREEZE_REOPEN_POLICY_TOKEN_PINNED`
- Cycle-005 artifact pointer:
  - `formal/output/cosmo_bg_micro05_package_freeze_reopen_policy_cycle01_v0.json`

Deliverable pointers:
- `formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md`
- `formal/output/cosmo_bg_micro05_package_freeze_reopen_policy_cycle01_v0.json`
- `formal/python/tests/test_cosmo_bg_micro05_package_freeze_reopen_policy_gate.py`
