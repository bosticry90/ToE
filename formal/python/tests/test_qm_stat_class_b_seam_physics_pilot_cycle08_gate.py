from __future__ import annotations

from qm_stat_class_b_cycle_gate_family_helper import QmStatCycleGateSpec, register_qm_stat_cycle_gate_suite


register_qm_stat_cycle_gate_suite(
    globals(),
    QmStatCycleGateSpec(
        cycle=8,
        doc_status_token="QM_STAT_CYCLE08_STATUS_v0: TWELFTH_CENTRAL_MOMENT_PARITY_AND_EXCLUSION_PINNED_NONCLAIM",
        blocker_doc_token="QM_STAT_CYCLE08_BLOCKER_DISCHARGE_CRITERIA_v0: MASS_MEAN_VARIANCE_THIRD_FOURTH_SIXTH_EIGHTH_TENTH_AND_TWELFTH_MOMENT_PARITY_REQUIRED",
        exclusion_doc_token="QM_STAT_CYCLE08_INCOMPATIBILITY_EXCLUSION_v0: TWELFTH_MOMENT_MISMATCH_FLAGGED_AS_NONCOMPATIBLE",
        scope_doc_token="QM_STAT_CYCLE08_SCOPE_v0: FINITE_STATE_DISCRETE_HIGHER_MOMENT_AUDIT_ONLY_NONCLAIM",
        cycle_status_doc_token="QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE08_STATUS_v0: CRITERIA_AND_TWELFTH_MOMENT_EXCLUSION_PINNED_NONCLAIM",
        artifact_status="CRITERIA_AND_TWELFTH_MOMENT_EXCLUSION_PINNED_NONCLAIM",
        criteria_token="MASS_MEAN_VARIANCE_THIRD_FOURTH_SIXTH_EIGHTH_TENTH_AND_TWELFTH_MOMENT_PARITY_REQUIRED",
        criteria_orders=(1, 2, 3, 4, 6, 8, 10, 12),
        exclusion_equal_orders=(1, 2, 3, 4, 6),
        exclusion_mismatch_orders=(8, 10, 12),
    ),
)
