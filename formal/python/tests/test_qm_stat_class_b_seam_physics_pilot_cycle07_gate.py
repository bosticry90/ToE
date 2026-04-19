from __future__ import annotations

from qm_stat_class_b_cycle_gate_family_helper import QmStatCycleGateSpec, register_qm_stat_cycle_gate_suite


register_qm_stat_cycle_gate_suite(
    globals(),
    QmStatCycleGateSpec(
        cycle=7,
        doc_status_token="QM_STAT_CYCLE07_STATUS_v0: TENTH_CENTRAL_MOMENT_PARITY_AND_EXCLUSION_PINNED_NONCLAIM",
        blocker_doc_token="QM_STAT_CYCLE07_BLOCKER_DISCHARGE_CRITERIA_v0: MASS_MEAN_VARIANCE_THIRD_FOURTH_SIXTH_EIGHTH_AND_TENTH_MOMENT_PARITY_REQUIRED",
        exclusion_doc_token="QM_STAT_CYCLE07_INCOMPATIBILITY_EXCLUSION_v0: TENTH_MOMENT_MISMATCH_FLAGGED_AS_NONCOMPATIBLE",
        scope_doc_token="QM_STAT_CYCLE07_SCOPE_v0: FINITE_STATE_DISCRETE_HIGHER_MOMENT_AUDIT_ONLY_NONCLAIM",
        cycle_status_doc_token="QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE07_STATUS_v0: CRITERIA_AND_TENTH_MOMENT_EXCLUSION_PINNED_NONCLAIM",
        artifact_status="CRITERIA_AND_TENTH_MOMENT_EXCLUSION_PINNED_NONCLAIM",
        criteria_token="MASS_MEAN_VARIANCE_THIRD_FOURTH_SIXTH_EIGHTH_AND_TENTH_MOMENT_PARITY_REQUIRED",
        criteria_orders=(1, 2, 3, 4, 6, 8, 10),
        exclusion_equal_orders=(1, 2, 3, 4, 6),
        exclusion_mismatch_orders=(8, 10),
    ),
)
