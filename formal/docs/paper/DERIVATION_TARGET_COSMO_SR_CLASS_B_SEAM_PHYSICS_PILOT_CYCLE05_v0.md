# Derivation Target: COSMO-SR Class-B Seam Physics Pilot Cycle05 v0

Spec ID:
- DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE05_v0

Target ID:
- TARGET-COSMO-SR-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE05-v0

Classification:
- P-PHYSICS

Purpose:
- Add one bounded non-redundant strengthening payload beyond COSMO-SR Cycle04.
- Extend low-z compatibility from sextic-corrected surrogate to octic-corrected surrogate against exact SR Doppler beta.
- Add one bounded high-z exclusion for octic-series surrogate drift.

Adjudication token:
- COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE05_ADJUDICATION: NOT_YET_DISCHARGED

Cycle04 predecessor anchors:
- formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE04_v0.md
- formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle04_v0.json
- formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle04_gate.py

Cycle05 bounded payload artifact:
- formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle05_v0.json

Cycle05 narrow gate:
- formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle05_gate.py

Cycle05 strengthening payload:
- COSMO_SR_CYCLE05_STATUS_v0: OCTIC_LOW_Z_ALIGNMENT_AND_EXCLUSION_PINNED_NONCLAIM
- COSMO_SR_CYCLE05_BLOCKER_DISCHARGE_CRITERIA_v0: EXACT_SR_DOPPLER_MATCH_OCTIC_IMPROVEMENT_REQUIRED
- COSMO_SR_CYCLE05_INCOMPATIBILITY_EXCLUSION_v0: HIGH_Z_OCTIC_SERIES_DRIFT_FLAGGED_AS_NONCOMPATIBLE
- COSMO_SR_CYCLE05_SCOPE_v0: FINITE_SAMPLE_LOW_Z_OCTIC_AUDIT_ONLY_NONCLAIM

Bounded blocker-discharge criteria:
1. finite low-z window `0 <= z <= z_max`.
2. exact SR Doppler map `beta_exact = (((1+z)^2)-1)/(((1+z)^2)+1)`.
3. sextic surrogate `beta_series6 = z - z^2/2 + z^4/4 - z^6/8`.
4. octic surrogate `beta_series8 = z - z^2/2 + z^4/4 - z^6/8 - z^8/16`.
5. bounded improvement requirement `|beta_exact-beta_series8| <= |beta_exact-beta_series6|` at each sample.

Bounded incompatibility exclusion payload:
- one explicit higher-z counterexample where octic surrogate drift is non-negligible,
- mismatch is marked `NONCOMPATIBLE_EXCLUDED_v0`.

Non-claim boundary:
- no seam class flip claim,
- no full theorem discharge claim,
- no global cosmology completion claim,
- no external truth claim.

Cycle05 status lock:
- COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE05_STATUS_v0: CRITERIA_AND_OCTIC_EXCLUSION_PINNED_NONCLAIM
