# Derivation Target: Cosmology Background Micro-02 Expansion-Law Surface v0

Spec ID:
- `DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_02_EXPANSION_LAW_SURFACE_v0`

Target ID:
- `TARGET-COSMO-BG-MICRO-02-EXPANSION-LAW-SURFACE-v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze Cycle-002 expansion-law surface deliverables for the cosmology background lane.
- Pin typed expansion-law placeholder surfaces before any closure promotion.
- Keep the lane bounded, non-claim, and scaffold-only by construction.

Adjudication token:
- `COSMO_BG_MICRO02_EXPANSION_ADJUDICATION: NOT_YET_DISCHARGED`

Scope-boundary token:
- `COSMO_BG_MICRO02_SCOPE_BOUNDARY_v0: EXPANSION_LAW_SURFACE_ONLY_NONCLAIM`

Progress token:
- `COSMO_BG_MICRO02_PROGRESS_v0: EXPANSION_LAW_SURFACE_TOKEN_PINNED`

Artifact token:
- `COSMO_BG_MICRO02_EXPANSION_SURFACE_ARTIFACT_v0: cosmo_bg_micro02_expansion_law_surface_cycle01_v0`

## TARGET section

- Expansion-law relation surface token:
  - `COSMO_BG_MICRO02_EXPANSION_RELATION_SURFACE_v0: HUBBLE_SCALE_FACTOR_RELATION_PLACEHOLDER_PINNED`
- Curvature contribution placeholder token:
  - `COSMO_BG_MICRO02_CURVATURE_SURFACE_v0: SPATIAL_CURVATURE_TERM_PLACEHOLDER_PINNED`
- Source contribution placeholder token:
  - `COSMO_BG_MICRO02_SOURCE_COUPLING_SURFACE_v0: EFFECTIVE_DENSITY_PRESSURE_COUPLING_PLACEHOLDER_PINNED`
- Regime assumptions placeholder token:
  - `COSMO_BG_MICRO02_REGIME_SURFACE_v0: HOMOGENEITY_ISOTROPY_BOUNDARY_PLACEHOLDER_PINNED`

## CANONICAL_ROUTE section

- Parent target pointer:
  - `formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md`

## BOUNDED_SCOPE section

- expansion-law scaffold scope only.
- no Einstein-equation closure claim.
- no Friedmann derivation closure claim.
- no perturbation-theory closure claim.
- no full cosmological model completion claim.
- no external truth claim.

## ADJUDICATION_SYNC section

- Cycle-002 micro adjudication token:
  - `COSMO_BG_MICRO02_EXPANSION_ADJUDICATION: NOT_YET_DISCHARGED`
- Cycle-002 micro progress token:
  - `COSMO_BG_MICRO02_PROGRESS_v0: EXPANSION_LAW_SURFACE_TOKEN_PINNED`
- Cycle-002 artifact pointer:
  - `formal/output/cosmo_bg_micro02_expansion_law_surface_cycle01_v0.json`

Deliverable pointers:
- `formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md`
- `formal/output/cosmo_bg_micro02_expansion_law_surface_cycle01_v0.json`
- `formal/python/tests/test_cosmo_bg_micro02_expansion_law_surface_gate.py`
