from __future__ import annotations

from qm_stat_class_b_synthesis_gate_family_helper import QmStatSynthesisGateSpec, register_qm_stat_synthesis_gate_suite


register_qm_stat_synthesis_gate_suite(
    globals(),
    QmStatSynthesisGateSpec(
        cycle_from=5,
        cycle_to=6,
        required_doc_tokens=(
            "QM_STAT_CYCLE05_BASELINE_v0: SIXTH_CENTRAL_MOMENT_PARITY_AND_EXCLUSION_PINNED",
            "QM_STAT_CYCLE06_ADDITIVE_DELTA_v0: EIGHTH_CENTRAL_MOMENT_PARITY_AND_EXCLUSION_PINNED",
            "QM_STAT_BLOCKER_DISCHARGE_IMPACT_v0: CRITERIA_STRENGTHENED_BUT_ADJUDICATION_STILL_OPEN",
            "QM_STAT_PROMOTION_BLOCKER_STATE_v0: CLASS_FLIP_AND_FULL_THEOREM_DISCHARGE_NOT_READY",
            "QM_STAT_NONCLAIM_BOUNDARY_STATE_v0: CLASS_FLIP_AND_FULL_DISCHARGE_NOT_CLAIMED",
            "QM_STAT_NEXT_DECISION_RULE_v0: IF_ONE_BOUNDED_ADDITIVE_QM_STAT_PAYLOAD_IS_READY_THEN_CYCLE07_ELSE_OPEN_COSMO_SR_CYCLE06",
            "QM_STAT_DECISION_BOUNDARY_STATUS_v0: SYNTHESIS_CHECKPOINT_READY",
            "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE05_TO_06_SYNTHESIS_STATUS_v0: CHECKPOINT_PINNED_NONCLAIM",
            "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE05_TO_06_SYNTHESIS_ADJUDICATION: NOT_YET_DISCHARGED",
        ),
        from_artifact_status="CRITERIA_AND_SIXTH_MOMENT_EXCLUSION_PINNED_NONCLAIM",
        to_artifact_status="CRITERIA_AND_EIGHTH_MOMENT_EXCLUSION_PINNED_NONCLAIM",
        from_criteria_token="MASS_MEAN_VARIANCE_THIRD_FOURTH_AND_SIXTH_MOMENT_PARITY_REQUIRED",
        to_criteria_token="MASS_MEAN_VARIANCE_THIRD_FOURTH_SIXTH_AND_EIGHTH_MOMENT_PARITY_REQUIRED",
        from_criteria_orders=(1, 2, 3, 4, 6),
        to_criteria_orders=(1, 2, 3, 4, 6, 8),
        newly_added_orders=(8,),
        exclusion_equal_orders=(1, 2, 3, 4, 6),
        exclusion_mismatch_orders=(8,),
    ),
)
