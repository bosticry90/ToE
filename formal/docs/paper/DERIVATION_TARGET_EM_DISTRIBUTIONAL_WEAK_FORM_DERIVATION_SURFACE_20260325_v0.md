# Derivation Target: EM Distributional Weak-Form Derivation Surface 20260325 v0

Spec ID:
- DERIVATION_TARGET_EM_DISTRIBUTIONAL_WEAK_FORM_DERIVATION_SURFACE_20260325_v0

Target ID:
- TARGET-EM-DISTRIBUTIONAL-WEAK-FORM-DERIVATION-SURFACE-20260325-v0

Classification:
- P-PHYSICS

Purpose:
- Add the first explicit weak-form derivation surface for the EM distributional lane.
- Keep the package bounded and non-claim while proving step-level symbolic consistency.
- Tie this surface directly to the prior EM distributional science increment artifact.

Adjudication token:
- EM_DISTRIBUTIONAL_WEAK_FORM_DERIVATION_20260325_ADJUDICATION: NOT_YET_DISCHARGED

## Derivation surface

- Prior artifact anchor:
  - formal/output/em_distributional_science_increment_20260325_v0.json
- New derivation artifact:
  - formal/output/em_distributional_weak_form_derivation_surface_20260325_v0.json

Canonical bounded weak-form route:
1. Choose one compactly-supported test function phi in C_c^infinity(omega).
2. Define distributional divergence pairing by duality.
3. Integrate by parts on bounded support and enforce vanishing boundary contribution from compact support.
4. Record symbolic identity:
   - <partial_mu J^mu, phi> = -<J^mu, partial_mu phi>
5. Pin one bounded singular-source compatibility witness in 1D model form.

## Scope boundaries

This package is explicitly bounded and non-claim:
- no theorem discharge claim,
- no curved-space covariant divergence claim,
- no non-Abelian completion claim,
- no external truth claim.

## Required markers

- EM_DISTRIBUTIONAL_WEAK_FORM_DERIVATION_STATUS_v0: BOUNDED_WEAK_FORM_DERIVATION_SURFACE_PINNED_NONCLAIM
- EM_DISTRIBUTIONAL_WEAK_FORM_IDENTITY_v0: PAIRING_DUALITY_INTEGRATION_BY_PARTS_SYMBOLIC_SURFACE
- EM_DISTRIBUTIONAL_WEAK_FORM_BOUNDARY_RULE_v0: COMPACT_SUPPORT_BOUNDARY_TERM_VANISHES
- EM_DISTRIBUTIONAL_WEAK_FORM_SOURCE_MODEL_v0: POINT_SOURCE_DELTA_SYMBOLIC_COMPATIBILITY
- EM_DISTRIBUTIONAL_WEAK_FORM_GATE_v0: formal/python/tests/test_em_distributional_weak_form_derivation_surface_gate.py

Deliverable pointers:
- formal/output/em_distributional_science_increment_20260325_v0.json
- formal/output/em_distributional_weak_form_derivation_surface_20260325_v0.json
- formal/python/tests/test_em_distributional_weak_form_derivation_surface_gate.py
