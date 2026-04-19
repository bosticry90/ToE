from __future__ import annotations

from qm_stat_class_b_cycle_gate_family_helper import QmStatCycleGateSpec, register_qm_stat_cycle_gate_suite


register_qm_stat_cycle_gate_suite(
    globals(),
    QmStatCycleGateSpec(
        cycle=2,
        doc_status_token="QM_STAT_CYCLE02_STATUS_v0: BLOCKER_CRITERIA_AND_EXCLUSION_CHECK_PINNED_NONCLAIM",
        blocker_doc_token="QM_STAT_CYCLE02_BLOCKER_DISCHARGE_CRITERIA_v0: MASS_NORMALIZATION_AND_MOMENT_PARITY_REQUIRED",
        exclusion_doc_token="QM_STAT_CYCLE02_INCOMPATIBILITY_EXCLUSION_v0: MASS_OR_MOMENT_MISMATCH_FLAGGED_AS_NONCOMPATIBLE",
        scope_doc_token="QM_STAT_CYCLE02_SCOPE_v0: FINITE_STATE_DISCRETE_EXCLUSION_AUDIT_ONLY_NONCLAIM",
        cycle_status_doc_token="QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE02_STATUS_v0: CRITERIA_AND_EXCLUSION_PAYLOAD_PINNED_NONCLAIM",
        artifact_status="CRITERIA_AND_EXCLUSION_PAYLOAD_PINNED_NONCLAIM",
        criteria_token="MASS_NORMALIZATION_AND_MOMENT_PARITY_REQUIRED",
        criteria_orders=(1, 2),
        exclusion_equal_orders=(),
        exclusion_mismatch_orders=(1,),
    ),
)
