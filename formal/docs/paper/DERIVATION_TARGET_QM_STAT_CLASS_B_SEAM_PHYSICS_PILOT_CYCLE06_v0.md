# Derivation Target: QM-STAT Class-B Seam Physics Pilot Cycle06 v0

Spec ID:
- DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE06_v0

Target ID:
- TARGET-QM-STAT-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE06-v0

Classification:
- P-PHYSICS

Purpose:
- Add one bounded non-redundant strengthening payload beyond Cycle05.
- Extend QM-STAT compatibility witness from sixth-central-moment parity to eighth-central-moment parity.
- Add bounded exclusion where lower central moments remain aligned while eighth-central-moment parity fails.

Adjudication token:
- QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE06_ADJUDICATION: NOT_YET_DISCHARGED

Cycle05 predecessor anchors:
- formal/docs/paper/DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE05_v0.md
- formal/output/qm_stat_class_b_seam_physics_pilot_cycle05_v0.json
- formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle05_gate.py

Cycle06 bounded payload artifact:
- formal/output/qm_stat_class_b_seam_physics_pilot_cycle06_v0.json

Cycle06 narrow gate:
- formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle06_gate.py

Cycle06 strengthening payload:
- QM_STAT_CYCLE06_STATUS_v0: EIGHTH_CENTRAL_MOMENT_PARITY_AND_EXCLUSION_PINNED_NONCLAIM
- QM_STAT_CYCLE06_BLOCKER_DISCHARGE_CRITERIA_v0: MASS_MEAN_VARIANCE_THIRD_FOURTH_SIXTH_AND_EIGHTH_MOMENT_PARITY_REQUIRED
- QM_STAT_CYCLE06_INCOMPATIBILITY_EXCLUSION_v0: EIGHTH_MOMENT_MISMATCH_FLAGGED_AS_NONCOMPATIBLE
- QM_STAT_CYCLE06_SCOPE_v0: FINITE_STATE_DISCRETE_HIGHER_MOMENT_AUDIT_ONLY_NONCLAIM

Bounded blocker-discharge criteria:
1. `sum_i p_i = 1` for both QM and STAT mass vectors.
2. first moment parity `mu_qm = mu_stat`.
3. second-central-moment parity `var_qm = var_stat`.
4. third-central-moment parity `m3_qm = m3_stat`.
5. fourth-central-moment parity `m4_qm = m4_stat`.
6. sixth-central-moment parity `m6_qm = m6_stat`.
7. eighth-central-moment parity `m8_qm = m8_stat`.

Bounded incompatibility exclusion payload:
- one explicit counterexample where first through sixth central moments remain aligned but eighth-central-moment parity fails,
- resulting mismatch is marked `NONCOMPATIBLE_EXCLUDED_v0`.

Non-claim boundary:
- no seam class flip claim,
- no full theorem discharge claim,
- no continuum statistical closure claim,
- no external truth claim.

Cycle06 status lock:
- QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE06_STATUS_v0: CRITERIA_AND_EIGHTH_MOMENT_EXCLUSION_PINNED_NONCLAIM
