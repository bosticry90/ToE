# Derivation Target: COSMO-SR Class-B Seam Physics Pilot Cycle01 v0

Spec ID:
- DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_v0

Target ID:
- TARGET-COSMO-SR-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE01-v0

Classification:
- P-PHYSICS

Purpose:
- Open the first bounded physics pilot for seam `SEAM-COSMO-SR`.
- Pin one typed seam witness package and one bounded physical compatibility payload.
- Keep this tranche non-promotional and non-claim while moving beyond counterfactual-only seam posture.

Adjudication token:
- COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_ADJUDICATION: NOT_YET_DISCHARGED

Pilot seam token:
- COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_SEAM_v0: SEAM-COSMO-SR
- COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CLASS_v0: TOE_CK_CLASS_COMPATIBILITY_v0

Required bounded pilot bundle:
1. Witness package pointer:
- formal/toe_formal/ToeFormal/Constraints/SeamWitnessPackages.lean

2. Source seam evidence anchors:
- formal/output/cosmo_m4_seam_closure_promotion_cycle01_v0.json
- formal/output/sr_m4_seam_closure_promotion_cycle01_v0.json

3. Bounded physics compatibility payload artifact:
- formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle01_v0.json

4. Narrow pilot gate:
- formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle01_gate.py

Bounded physical compatibility payload (cycle01):
- COSMO_SR_COMPATIBILITY_PAYLOAD_STATUS_v0: BOUNDED_LOW_Z_KINEMATIC_ALIGNMENT_PINNED_NONCLAIM
- COSMO_SR_COMPATIBILITY_ROUTE_v0: LOW_Z_REDSHIFT_TO_SR_BETA_LINEARIZATION_BRIDGE
- COSMO_SR_COMPATIBILITY_WITNESS_v0: LOW_Z_LINEAR_POINTWISE_ALIGNMENT
- COSMO_SR_COMPATIBILITY_SCOPE_v0: LOW_Z_WINDOW_ONLY_NONCLAIM

Bounded witness model:
1. low-z redshift window `0 <= z <= z_max`,
2. SR low-beta linearization `beta_sr_linear = z`,
3. COSMO kinematic linearization `beta_cosmo_linear = z`,
4. bounded pointwise alignment check `|beta_sr_linear - beta_cosmo_linear| <= epsilon`,
5. explicit high-z exclusion where linearization drift is non-negligible.

Bounded incompatibility exclusion payload:
- high-z counterexample at `z = 1/2`,
- linear SR beta (`1/2`) is not treated as equivalent to relativistic exact beta,
- counterexample is explicitly classified as `NONCOMPATIBLE_EXCLUDED_v0`.

Non-claim boundary:
- no seam class flip claim,
- no full theorem discharge claim,
- no global cosmology completion claim,
- no external truth claim.

Cycle01 status lock:
- COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_STATUS_v0: WITNESS_AND_BOUNDED_PAYLOAD_PINNED_NONCLAIM
