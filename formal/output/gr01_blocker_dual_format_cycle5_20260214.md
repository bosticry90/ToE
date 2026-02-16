# GR01 Blocker/Dual-Format Sync (Cycle-005, 2026-02-14)

## Goal

Adopt dual-format closure reporting while keeping canonical pillar governance
strict, and advance blocker-facing surfaces for `TOE-GR-DER-02` and
`TOE-GR-CONS-01` without over-claiming closure.

## Changes

1. Dual-layer closure semantics added to roadmap:
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- tokens:
  - `PILLAR-GR_PHYSICS_STATUS: CLOSED_v0_DISCRETE_CONDITIONAL`
  - `PILLAR-GR_GOVERNANCE_STATUS: BLOCKED_v0_DER02_CONS01`

2. Results sync:
- `formal/docs/paper/RESULTS_TABLE_v0.md`
- added policy row `GR-CLS-STATUS-01`.
- kept `TOE-GR-DER-02` and `TOE-GR-CONS-01` as `B-BLOCKED`.
- updated `TOE-GR-CONS-01` evidence/status text to include new contract-level
  theorem token while remaining blocked.

3. Blocker docs enriched with explicit unblock bundles:
- `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md`
- `formal/docs/paper/TOE_GR01_CONSERVATION_COMPATIBILITY_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_GR_CONSERVATION_OBJECT_v0.md`

4. Conservation theorem-surface progress:
- `formal/toe_formal/ToeFormal/GR/ConservationContract.lean`
- added:
  - `DiscreteGradient1D`
  - `DiscreteDivergence1D`
  - `PoissonFluxCompatibility1D`
  - `gr01_conservation_compatibility_from_poisson_residual_v0`

5. New synchronization gate test:
- `formal/python/tests/test_gr01_dual_closure_and_blockers.py`

## Verification

- Lean: `formal/toe_formal/build.ps1 ToeFormal.GR.ConservationContract`
- Python: `.\py.ps1 -m pytest formal/python/tests -q`
