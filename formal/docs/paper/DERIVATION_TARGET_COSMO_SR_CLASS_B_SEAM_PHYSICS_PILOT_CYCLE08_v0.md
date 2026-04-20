# Derivation Target: COSMO-SR Class-B Seam Physics Pilot Cycle08 v0

Spec ID:
- DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE08_v0

Target ID:
- TARGET-COSMO-SR-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE08-v0

Classification:
- P-PHYSICS

Purpose:
- Add one bounded non-redundant strengthening payload beyond COSMO-SR Cycle07.
- Extend low-z compatibility from dodecic-corrected surrogate to tetradecic-corrected surrogate against exact SR Doppler beta.
- Add one bounded high-z exclusion for tetradecic-series drift.

Adjudication token:
- COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE08_ADJUDICATION: NOT_YET_DISCHARGED

Cycle07 predecessor anchors:
- formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE07_v0.md
- formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle07_v0.json
- formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle07_gate.py

Cycle08 bounded payload artifact:
- formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle08_v0.json

Cycle08 narrow gate:
- formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle08_gate.py

Cycle08 strengthening payload:
- COSMO_SR_CYCLE08_STATUS_v0: TETRADECIC_LOW_Z_ALIGNMENT_AND_EXCLUSION_PINNED_NONCLAIM
- COSMO_SR_CYCLE08_BLOCKER_DISCHARGE_CRITERIA_v0: EXACT_SR_DOPPLER_MATCH_TETRADECIC_IMPROVEMENT_REQUIRED
- COSMO_SR_CYCLE08_INCOMPATIBILITY_EXCLUSION_v0: HIGH_Z_TETRADECIC_SERIES_DRIFT_FLAGGED_AS_NONCOMPATIBLE
- COSMO_SR_CYCLE08_SCOPE_v0: FINITE_SAMPLE_LOW_Z_TETRADECIC_AUDIT_ONLY_NONCLAIM

Bounded blocker-discharge criteria:
1. finite low-z window `0 <= z <= z_max`.
2. exact SR Doppler map `beta_exact = (((1+z)^2)-1)/(((1+z)^2)+1)`.
3. dodecic surrogate `beta_series12 = z - z^2/2 + z^4/4 - z^6/8 - z^8/16 - z^10/32 - z^12/64`.
4. tetradecic surrogate `beta_series14 = z - z^2/2 + z^4/4 - z^6/8 - z^8/16 - z^10/32 - z^12/64 - z^14/128`.
5. bounded improvement requirement `|beta_exact-beta_series14| <= |beta_exact-beta_series12|` at each sample.

Bounded incompatibility exclusion payload:
- one explicit higher-z counterexample where tetradecic surrogate drift is non-negligible,
- mismatch is marked `NONCOMPATIBLE_EXCLUDED_v0`.

Non-claim boundary:
- no seam class flip claim,
- no full theorem discharge claim,
- no global cosmology completion claim,
- no external truth claim.

Cycle08 status lock:
- COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE08_STATUS_v0: CRITERIA_AND_TETRADECIC_EXCLUSION_PINNED_NONCLAIM