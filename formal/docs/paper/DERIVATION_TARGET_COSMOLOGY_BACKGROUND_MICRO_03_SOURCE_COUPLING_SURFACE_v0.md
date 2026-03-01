# Derivation Target: Cosmology Background Micro-03 Source-Coupling Surface v0

Spec ID:
- `DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_03_SOURCE_COUPLING_SURFACE_v0`

Target ID:
- `TARGET-COSMO-BG-MICRO-03-SOURCE-COUPLING-SURFACE-v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze Cycle-003 source-coupling surface deliverables for the cosmology background lane.
- Pin typed source-sector coupling placeholders before any closure promotion.
- Keep the lane bounded, non-claim, and scaffold-only by construction.

Adjudication token:
- `COSMO_BG_MICRO03_SOURCE_COUPLING_ADJUDICATION: NOT_YET_DISCHARGED`

Scope-boundary token:
- `COSMO_BG_MICRO03_SCOPE_BOUNDARY_v0: SOURCE_COUPLING_SURFACE_ONLY_NONCLAIM`

Progress token:
- `COSMO_BG_MICRO03_PROGRESS_v0: SOURCE_COUPLING_SURFACE_TOKEN_PINNED`

Artifact token:
- `COSMO_BG_MICRO03_SOURCE_COUPLING_ARTIFACT_v0: cosmo_bg_micro03_source_coupling_surface_cycle01_v0`

## TARGET section

- Effective density coupling surface token:
  - `COSMO_BG_MICRO03_DENSITY_COUPLING_SURFACE_v0: EFFECTIVE_DENSITY_COUPLING_PLACEHOLDER_PINNED`
- Pressure coupling surface token:
  - `COSMO_BG_MICRO03_PRESSURE_COUPLING_SURFACE_v0: EFFECTIVE_PRESSURE_COUPLING_PLACEHOLDER_PINNED`
- Equation-of-state placeholder token:
  - `COSMO_BG_MICRO03_EOS_SURFACE_v0: EQUATION_OF_STATE_PLACEHOLDER_PINNED`
- Regime coupling boundary token:
  - `COSMO_BG_MICRO03_REGIME_SURFACE_v0: SOURCE_COUPLING_REGIME_BOUNDARY_PLACEHOLDER_PINNED`

## CANONICAL_ROUTE section

- Parent target pointer:
  - `formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md`

## BOUNDED_SCOPE section

- source-coupling scaffold scope only.
- no Einstein-equation closure claim.
- no Friedmann derivation closure claim.
- no perturbation-theory closure claim.
- no full cosmological model completion claim.
- no external truth claim.

## ADJUDICATION_SYNC section

- Cycle-003 micro adjudication token:
  - `COSMO_BG_MICRO03_SOURCE_COUPLING_ADJUDICATION: NOT_YET_DISCHARGED`
- Cycle-003 micro progress token:
  - `COSMO_BG_MICRO03_PROGRESS_v0: SOURCE_COUPLING_SURFACE_TOKEN_PINNED`
- Cycle-003 artifact pointer:
  - `formal/output/cosmo_bg_micro03_source_coupling_surface_cycle01_v0.json`

Deliverable pointers:
- `formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md`
- `formal/output/cosmo_bg_micro03_source_coupling_surface_cycle01_v0.json`
- `formal/python/tests/test_cosmo_bg_micro03_source_coupling_surface_gate.py`
