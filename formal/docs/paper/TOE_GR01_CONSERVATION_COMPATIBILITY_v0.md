# TOE-GR-01 Conservation Compatibility v0

Spec ID:
- `TOE_GR01_CONSERVATION_COMPATIBILITY_v0`

Classification:
- `T-CONDITIONAL`

Purpose:
- Define a minimal, bounded conservation-compatibility surface for GR01 weak-field closure.
- Prevent conservation-language drift while full GR conservation theorem families remain unclosed.

Scope:
- Weak-field/default-quotient GR01 lane only.
- Compatibility-level statement, not a full conservation derivation.

## Minimal Compatibility Statement

- Canonical weak-field compatibility target:
  - divergence/source compatibility posture for the Poisson-form sector.
- Reporting-level form:
  - `nabla · g = -kappa * rho` with `g = -grad(Phi)` in bounded weak-field interpretation.
- Current status:
  - compatibility target is explicit and pinned,
  - theorem-surface compatibility is discharged under explicit bridge assumptions,
  - full GR conservation-family closure remains out of scope for v0.

Adjudication token:
- `CONS01_ADJUDICATION: DISCHARGED_CONDITIONAL_v0`

## Dependencies

- `formal/docs/paper/DERIVATION_TARGET_GR_CONSERVATION_OBJECT_v0.md`
- `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md`
- `formal/docs/paper/TOE_GR01_LAPLACIAN_EXTRACTION_v0.md`
- `formal/docs/paper/TOE_GR01_THEOREM_SURFACE_v0.md`

## Promotion / Maintenance Boundary

- This artifact is now maintained at `T-CONDITIONAL` only while:
  - theorem-surface conservation compatibility tokens remain pinned,
  - assumption IDs and scope limits remain explicit in `ASSUMPTION_REGISTRY_v1.md`,
  - enforcement tests continue to pin theorem tokens and non-claim wording.

## Promotion Execution Bundle (CONS-01, v0)

Implemented theorem-surface tokens:
- `formal/toe_formal/ToeFormal/GR/ConservationContract.lean`
  - `gr01_conservation_compatibility_from_poisson_residual_v0`
  - `gr01_conservation_compatibility_from_bridge_promotion_chain_v0`
  - contract-level statement: discrete Poisson residual closure implies
    discrete divergence/source compatibility in bounded 1D weak-field scope.
  - bridge-promotion statement: GR01 bridge assumptions imply discrete residual
    closure, which then implies flux/divergence compatibility.

Pinned assumption bindings:
1. `ASM-GR01-CONS-01` (structural bridge composition from residual closure to
   compatibility surface).
2. `ASM-GR01-CONS-02` (regime/approximation inheritance via bridge-promotion
   assumptions).

Enforcement hook:
- `formal/python/tests/test_gr01_dual_closure_and_blockers.py`
  - if `TOE-GR-CONS-01` is non-`B-*`, the two conservation theorem tokens above
    and assumption bindings must exist, and non-claim boundary lines must remain.

Remaining open layer (explicitly out of scope for this promotion):
- theorem-complete GR conservation family closure (full Noether-grade family).

## Non-claim Boundary

- This artifact does not claim full GR conservation-law recovery.
- This artifact does not claim Noether-theorem completion.
- This artifact does not claim external truth.
