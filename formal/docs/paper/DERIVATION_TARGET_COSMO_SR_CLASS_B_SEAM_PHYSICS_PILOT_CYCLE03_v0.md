# Derivation Target: COSMO-SR Class-B Seam Physics Pilot Cycle03 v0

Spec ID:
- DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE03_v0

Target ID:
- TARGET-COSMO-SR-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE03-v0

Classification:
- P-PHYSICS

Purpose:
- Add one bounded non-redundant strengthening payload beyond COSMO-SR Cycle02.
- Extend low-z compatibility from second-order surrogate to quartic-corrected surrogate against exact SR Doppler beta.
- Add one bounded high-z exclusion for quartic-series surrogate breakdown.

Adjudication token:
- COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE03_ADJUDICATION: NOT_YET_DISCHARGED

Cycle02 predecessor anchors:
- formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE02_v0.md
- formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle02_v0.json
- formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle02_gate.py

Cycle03 bounded payload artifact:
- formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle03_v0.json

Cycle03 narrow gate:
- formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle03_gate.py

Cycle03 strengthening payload:
- COSMO_SR_CYCLE03_STATUS_v0: QUARTIC_LOW_Z_ALIGNMENT_AND_EXCLUSION_PINNED_NONCLAIM
- COSMO_SR_CYCLE03_BLOCKER_DISCHARGE_CRITERIA_v0: EXACT_SR_DOPPLER_MATCH_QUARTIC_IMPROVEMENT_REQUIRED
- COSMO_SR_CYCLE03_INCOMPATIBILITY_EXCLUSION_v0: HIGH_Z_QUARTIC_SERIES_DRIFT_FLAGGED_AS_NONCOMPATIBLE
- COSMO_SR_CYCLE03_SCOPE_v0: FINITE_SAMPLE_LOW_Z_QUARTIC_AUDIT_ONLY_NONCLAIM

Bounded blocker-discharge criteria:
1. finite low-z window `0 <= z <= z_max`.
2. exact SR Doppler map `beta_exact = (((1+z)^2)-1)/(((1+z)^2)+1)`.
3. second-order surrogate `beta_series2 = z - z^2/2`.
4. quartic surrogate `beta_series4 = z - z^2/2 + z^4/4`.
5. bounded improvement requirement `|beta_exact-beta_series4| <= |beta_exact-beta_series2|` at each sample.

Bounded incompatibility exclusion payload:
- one explicit higher-z counterexample where quartic surrogate drift is non-negligible,
- mismatch is marked `NONCOMPATIBLE_EXCLUDED_v0`.

Non-claim boundary:
- no seam class flip claim,
- no full theorem discharge claim,
- no global cosmology completion claim,
- no external truth claim.

Cycle03 status lock:
- COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE03_STATUS_v0: CRITERIA_AND_QUARTIC_EXCLUSION_PINNED_NONCLAIM
