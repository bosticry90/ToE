# Derivation Target: QM-STAT Class-B Seam Physics Pilot Cycle04 v0

Spec ID:
- DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE04_v0

Target ID:
- TARGET-QM-STAT-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE04-v0

Classification:
- P-PHYSICS

Purpose:
- Add one bounded non-redundant strengthening payload beyond Cycle03.
- Extend QM-STAT compatibility witness from third-central-moment parity to fourth-central-moment parity.
- Add bounded exclusion where first/second/third moments align but fourth-central-moment parity fails.

Adjudication token:
- QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE04_ADJUDICATION: NOT_YET_DISCHARGED

Cycle03 predecessor anchors:
- formal/docs/paper/DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE03_v0.md
- formal/output/qm_stat_class_b_seam_physics_pilot_cycle03_v0.json
- formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle03_gate.py

Cycle04 bounded payload artifact:
- formal/output/qm_stat_class_b_seam_physics_pilot_cycle04_v0.json

Cycle04 narrow gate:
- formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle04_gate.py

Cycle04 strengthening payload:
- QM_STAT_CYCLE04_STATUS_v0: FOURTH_CENTRAL_MOMENT_PARITY_AND_EXCLUSION_PINNED_NONCLAIM
- QM_STAT_CYCLE04_BLOCKER_DISCHARGE_CRITERIA_v0: MASS_MEAN_VARIANCE_THIRD_AND_FOURTH_MOMENT_PARITY_REQUIRED
- QM_STAT_CYCLE04_INCOMPATIBILITY_EXCLUSION_v0: FOURTH_MOMENT_MISMATCH_FLAGGED_AS_NONCOMPATIBLE
- QM_STAT_CYCLE04_SCOPE_v0: FINITE_STATE_DISCRETE_HIGHER_MOMENT_AUDIT_ONLY_NONCLAIM

Bounded blocker-discharge criteria:
1. `sum_i p_i = 1` for both QM and STAT mass vectors.
2. first moment parity `mu_qm = mu_stat`.
3. second-central-moment parity `var_qm = var_stat`.
4. third-central-moment parity `m3_qm = m3_stat`.
5. fourth-central-moment parity `m4_qm = m4_stat`.

Bounded incompatibility exclusion payload:
- one explicit counterexample where first/second/third moments remain aligned but fourth-central-moment parity fails,
- resulting mismatch is marked `NONCOMPATIBLE_EXCLUDED_v0`.

Non-claim boundary:
- no seam class flip claim,
- no full theorem discharge claim,
- no continuum statistical closure claim,
- no external truth claim.

Cycle04 status lock:
- QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE04_STATUS_v0: CRITERIA_AND_FOURTH_MOMENT_EXCLUSION_PINNED_NONCLAIM
