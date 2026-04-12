from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_MODE_STRIKE_SUMMARY_20260411_v0"

PACKET41_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "packet41_successor_decision_enforcement_20260411_v0.json"
)
PACKET41_REWORK_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "packet41_numeric_clearance_rework_tranche_20260411_v0.json"
)
PACKET41_DECOMP_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "packet41_review_layer_clearance_decomposition_20260411_v0.json"
)
PACKET41_COMPONENT_LIFT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "packet41_component_lift_tranche_20260411_v0.json"
)
PACKET41_RETRO_COMPONENT_LIFT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "packet41_component_lift_retrospective_tranche_20260411_v0.json"
)
PACKET41_BRANCH_DECISION_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "packet41_branch_decision_tranche_20260411_v0.json"
)
POST_PACKET41_RECLASSIFICATION_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_packet41_reclassification_next_lane_tranche_20260411_v0.json"
)
QM_BOUNDED_STOP_RULE_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_qm_bounded_stop_rule_decision_20260411_v0.json"
)
POST_QM_RECLASSIFICATION_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_qm_reclassification_next_lane_tranche_20260411_v0.json"
)
GR_SUBTARGET_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_gr_subtarget_tranche_20260411_v0.json"
)
GR_BOUNDED_STOP_RULE_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_gr_bounded_stop_rule_decision_20260411_v0.json"
)
STAT_SUBTARGET_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_stat_subtarget_tranche_20260411_v0.json"
)
STAT_BOUNDED_STOP_RULE_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_stat_bounded_stop_rule_decision_20260411_v0.json"
)
COSMO_SUBTARGET_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_cosmo_subtarget_tranche_20260411_v0.json"
)
COSMO_BOUNDED_STOP_RULE_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_cosmo_bounded_stop_rule_decision_20260411_v0.json"
)
SCIENCE_ATTACK_STYLE_RETHINK_DECISION_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "science_attack_style_rethink_decision_20260411_v0.json"
)
SIMULATION_FIRST_PACKET_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "simulation_first_falsification_packet_report_20260411_v0.json"
)
SIMULATION_FIRST_CAMPAIGN_DECISION_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "simulation_first_falsification_campaign_decision_20260411_v0.json"
)
SIMULATION_FIRST_PACKET_V1_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "simulation_first_falsification_packet_report_20260411_v1.json"
)
SIMULATION_FIRST_CAMPAIGN_V1_DECISION_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "simulation_first_falsification_campaign_decision_20260411_v1.json"
)
SIMULATION_FIRST_PACKET_V2_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "simulation_first_falsification_packet_report_20260411_v2.json"
)
SIMULATION_FIRST_CAMPAIGN_V2_DECISION_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "simulation_first_falsification_campaign_decision_20260411_v2.json"
)
SIMULATION_FIRST_PACKET_V3_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "simulation_first_falsification_packet_report_20260411_v3.json"
)
SIMULATION_FIRST_CAMPAIGN_V3_DECISION_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "simulation_first_falsification_campaign_decision_20260411_v3.json"
)
BROADER_SEAM_REDESIGN_TRANCHE_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "broader_seam_package_redesign_tranche_report_20260411_v0.json"
)
BROADER_SEAM_REDESIGN_DECISION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "broader_seam_package_redesign_decision_20260411_v0.json"
)
EXTERNAL_BENCHMARK_PACKET_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "external_discriminative_benchmark_packet_report_20260411_v0.json"
)
EXTERNAL_BENCHMARK_DECISION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "external_discriminative_benchmark_decision_20260411_v0.json"
)
FUNDAMENTAL_RETHINK_PACKET_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "fundamental_attack_strategy_rethink_packet_report_20260411_v0.json"
)
FUNDAMENTAL_RETHINK_DECISION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "fundamental_attack_strategy_rethink_decision_20260411_v0.json"
)
PROOF_DEBT_FIRST_PACKET_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "proof_debt_first_formal_campaign_packet_report_20260411_v0.json"
)
PROOF_DEBT_FIRST_DECISION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "proof_debt_first_formal_campaign_decision_20260411_v0.json"
)
PROOF_DEBT_FIRST_DISCHARGE_TRANCHE_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "proof_debt_first_formal_campaign_discharge_tranche_report_20260411_v0.json"
)
PROOF_DEBT_FIRST_DISCHARGE_DECISION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "proof_debt_first_formal_campaign_discharge_decision_20260411_v0.json"
)
PROOF_DEBT_EMU1_GATE_COMPLETION_TRANCHE_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "proof_debt_emu1_gate_surface_completion_tranche_report_20260411_v0.json"
)
PROOF_DEBT_EMU1_GATE_COMPLETION_DECISION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "proof_debt_emu1_gate_surface_completion_decision_20260411_v0.json"
)
PROOF_DEBT_CLUSTER_BRANCH_RULING_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "proof_debt_cluster_branch_ruling_report_20260411_v0.json"
)
PROOF_DEBT_NEXT_CLUSTER_SELECTION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "proof_debt_next_cluster_selection_report_20260411_v0.json"
)
PACKET41_TARGETED_EVIDENCE_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "packet41_targeted_justification_evidence_injection_tranche_20260411_v0.json"
)
PACKET41_HOLD_FORK_EVIDENCE_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "packet41_hold_fork_evidence_injection_tranche_20260411_v0.json"
)
QM_SUBTARGET_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_qm_subtarget_tranche_20260411_v0.json"
)
QM_SUBTARGET_REPORT_V1_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_qm_subtarget_tranche_20260411_v1.json"
)
TREND_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json"
LEDGER_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json"
BASELINE_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "science_global_completion_baseline_20260411_v0.json"
)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    try:
        return str(path.relative_to(REPO_ROOT)).replace("\\", "/")
    except ValueError:
        return str(path).replace("\\", "/")


def _classify_outcome(criteria: dict[str, bool]) -> str:
    if any(criteria.values()):
        return "SUCCESS"
    return "NO_CHANGE"


def build_summary(
    captured_at_utc: str | None,
    external_report_path: str | None,
    external_packet_mode: str | None,
    qm_fallback_executed: bool,
    packet41_only: bool,
    packet41_component_target: str,
) -> dict[str, Any]:
    packet41 = _read_json(PACKET41_REPORT_PATH)
    packet41_rework = _read_json(PACKET41_REWORK_PATH)
    packet41_decomp = _read_json(PACKET41_DECOMP_PATH)
    packet41_component_lift = _read_json(PACKET41_COMPONENT_LIFT_PATH)
    packet41_retro_component_lift = None
    if PACKET41_RETRO_COMPONENT_LIFT_PATH.exists():
        packet41_retro_component_lift = _read_json(PACKET41_RETRO_COMPONENT_LIFT_PATH)
    packet41_branch_decision = None
    if PACKET41_BRANCH_DECISION_PATH.exists():
        packet41_branch_decision = _read_json(PACKET41_BRANCH_DECISION_PATH)
    post_packet41_reclassification = None
    if POST_PACKET41_RECLASSIFICATION_PATH.exists():
        post_packet41_reclassification = _read_json(POST_PACKET41_RECLASSIFICATION_PATH)
    qm_bounded_stop_rule = None
    if QM_BOUNDED_STOP_RULE_PATH.exists():
        qm_bounded_stop_rule = _read_json(QM_BOUNDED_STOP_RULE_PATH)
    post_qm_reclassification = None
    if POST_QM_RECLASSIFICATION_PATH.exists():
        post_qm_reclassification = _read_json(POST_QM_RECLASSIFICATION_PATH)
    gr_subtarget = None
    if GR_SUBTARGET_REPORT_PATH.exists():
        gr_subtarget = _read_json(GR_SUBTARGET_REPORT_PATH)
    gr_bounded_stop_rule = None
    if GR_BOUNDED_STOP_RULE_PATH.exists():
        gr_bounded_stop_rule = _read_json(GR_BOUNDED_STOP_RULE_PATH)
    stat_subtarget = None
    if STAT_SUBTARGET_REPORT_PATH.exists():
        stat_subtarget = _read_json(STAT_SUBTARGET_REPORT_PATH)
    stat_bounded_stop_rule = None
    if STAT_BOUNDED_STOP_RULE_PATH.exists():
        stat_bounded_stop_rule = _read_json(STAT_BOUNDED_STOP_RULE_PATH)
    cosmo_subtarget = None
    if COSMO_SUBTARGET_REPORT_PATH.exists():
        cosmo_subtarget = _read_json(COSMO_SUBTARGET_REPORT_PATH)
    cosmo_bounded_stop_rule = None
    if COSMO_BOUNDED_STOP_RULE_PATH.exists():
        cosmo_bounded_stop_rule = _read_json(COSMO_BOUNDED_STOP_RULE_PATH)
    science_attack_style_rethink = None
    if SCIENCE_ATTACK_STYLE_RETHINK_DECISION_PATH.exists():
        science_attack_style_rethink = _read_json(SCIENCE_ATTACK_STYLE_RETHINK_DECISION_PATH)
    simulation_first_packet = None
    if SIMULATION_FIRST_PACKET_REPORT_PATH.exists():
        simulation_first_packet = _read_json(SIMULATION_FIRST_PACKET_REPORT_PATH)
    simulation_first_campaign_decision = None
    if SIMULATION_FIRST_CAMPAIGN_DECISION_PATH.exists():
        simulation_first_campaign_decision = _read_json(SIMULATION_FIRST_CAMPAIGN_DECISION_PATH)
    simulation_first_packet_v1 = None
    if SIMULATION_FIRST_PACKET_V1_REPORT_PATH.exists():
        simulation_first_packet_v1 = _read_json(SIMULATION_FIRST_PACKET_V1_REPORT_PATH)
    simulation_first_campaign_v1_decision = None
    if SIMULATION_FIRST_CAMPAIGN_V1_DECISION_PATH.exists():
        simulation_first_campaign_v1_decision = _read_json(SIMULATION_FIRST_CAMPAIGN_V1_DECISION_PATH)
    simulation_first_packet_v2 = None
    if SIMULATION_FIRST_PACKET_V2_REPORT_PATH.exists():
        simulation_first_packet_v2 = _read_json(SIMULATION_FIRST_PACKET_V2_REPORT_PATH)
    simulation_first_campaign_v2_decision = None
    if SIMULATION_FIRST_CAMPAIGN_V2_DECISION_PATH.exists():
        simulation_first_campaign_v2_decision = _read_json(SIMULATION_FIRST_CAMPAIGN_V2_DECISION_PATH)
    simulation_first_packet_v3 = None
    if SIMULATION_FIRST_PACKET_V3_REPORT_PATH.exists():
        simulation_first_packet_v3 = _read_json(SIMULATION_FIRST_PACKET_V3_REPORT_PATH)
    simulation_first_campaign_v3_decision = None
    if SIMULATION_FIRST_CAMPAIGN_V3_DECISION_PATH.exists():
        simulation_first_campaign_v3_decision = _read_json(SIMULATION_FIRST_CAMPAIGN_V3_DECISION_PATH)
    broader_seam_redesign_tranche = None
    if BROADER_SEAM_REDESIGN_TRANCHE_REPORT_PATH.exists():
        broader_seam_redesign_tranche = _read_json(BROADER_SEAM_REDESIGN_TRANCHE_REPORT_PATH)
    broader_seam_redesign_decision = None
    if BROADER_SEAM_REDESIGN_DECISION_REPORT_PATH.exists():
        broader_seam_redesign_decision = _read_json(BROADER_SEAM_REDESIGN_DECISION_REPORT_PATH)
    external_benchmark_packet = None
    if EXTERNAL_BENCHMARK_PACKET_REPORT_PATH.exists():
        external_benchmark_packet = _read_json(EXTERNAL_BENCHMARK_PACKET_REPORT_PATH)
    external_benchmark_decision = None
    if EXTERNAL_BENCHMARK_DECISION_REPORT_PATH.exists():
        external_benchmark_decision = _read_json(EXTERNAL_BENCHMARK_DECISION_REPORT_PATH)
    fundamental_rethink_packet = None
    if FUNDAMENTAL_RETHINK_PACKET_REPORT_PATH.exists():
        fundamental_rethink_packet = _read_json(FUNDAMENTAL_RETHINK_PACKET_REPORT_PATH)
    fundamental_rethink_decision = None
    if FUNDAMENTAL_RETHINK_DECISION_REPORT_PATH.exists():
        fundamental_rethink_decision = _read_json(FUNDAMENTAL_RETHINK_DECISION_REPORT_PATH)
    proof_debt_first_packet = None
    if PROOF_DEBT_FIRST_PACKET_REPORT_PATH.exists():
        proof_debt_first_packet = _read_json(PROOF_DEBT_FIRST_PACKET_REPORT_PATH)
    proof_debt_first_decision = None
    if PROOF_DEBT_FIRST_DECISION_REPORT_PATH.exists():
        proof_debt_first_decision = _read_json(PROOF_DEBT_FIRST_DECISION_REPORT_PATH)
    proof_debt_first_discharge_tranche = None
    if PROOF_DEBT_FIRST_DISCHARGE_TRANCHE_REPORT_PATH.exists():
        proof_debt_first_discharge_tranche = _read_json(PROOF_DEBT_FIRST_DISCHARGE_TRANCHE_REPORT_PATH)
    proof_debt_first_discharge_decision = None
    if PROOF_DEBT_FIRST_DISCHARGE_DECISION_REPORT_PATH.exists():
        proof_debt_first_discharge_decision = _read_json(PROOF_DEBT_FIRST_DISCHARGE_DECISION_REPORT_PATH)
    proof_debt_emu1_gate_completion_tranche = None
    if PROOF_DEBT_EMU1_GATE_COMPLETION_TRANCHE_REPORT_PATH.exists():
        proof_debt_emu1_gate_completion_tranche = _read_json(PROOF_DEBT_EMU1_GATE_COMPLETION_TRANCHE_REPORT_PATH)
    proof_debt_emu1_gate_completion_decision = None
    if PROOF_DEBT_EMU1_GATE_COMPLETION_DECISION_REPORT_PATH.exists():
        proof_debt_emu1_gate_completion_decision = _read_json(PROOF_DEBT_EMU1_GATE_COMPLETION_DECISION_REPORT_PATH)
    proof_debt_cluster_branch_ruling = None
    if PROOF_DEBT_CLUSTER_BRANCH_RULING_REPORT_PATH.exists():
        proof_debt_cluster_branch_ruling = _read_json(PROOF_DEBT_CLUSTER_BRANCH_RULING_REPORT_PATH)
    proof_debt_next_cluster_selection = None
    if PROOF_DEBT_NEXT_CLUSTER_SELECTION_REPORT_PATH.exists():
        proof_debt_next_cluster_selection = _read_json(PROOF_DEBT_NEXT_CLUSTER_SELECTION_REPORT_PATH)
    targeted_evidence = None
    if PACKET41_TARGETED_EVIDENCE_PATH.exists():
        targeted_evidence = _read_json(PACKET41_TARGETED_EVIDENCE_PATH)
    hold_fork_evidence = None
    if PACKET41_HOLD_FORK_EVIDENCE_PATH.exists():
        hold_fork_evidence = _read_json(PACKET41_HOLD_FORK_EVIDENCE_PATH)
    qm_path = QM_SUBTARGET_REPORT_V1_PATH if QM_SUBTARGET_REPORT_V1_PATH.exists() else QM_SUBTARGET_REPORT_PATH
    qm = _read_json(qm_path)
    trend = _read_json(TREND_PATH)
    ledger = _read_json(LEDGER_PATH)
    baseline = _read_json(BASELINE_PATH)

    prior = trend.get("blocker_counts", {}).get("prior", {})
    current = trend.get("blocker_counts", {}).get("current", {})

    theorem_gap_prior = int(prior.get("THEOREM_GAP", 0))
    theorem_gap_current = int(current.get("THEOREM_GAP", theorem_gap_prior))
    seam_gap_prior = int(prior.get("SEAM_INTEGRATION_GAP", 0))
    seam_gap_current = int(current.get("SEAM_INTEGRATION_GAP", seam_gap_prior))

    packet41_inputs = packet41.get("objective_quality", {}).get("inputs", {})
    packet41_cycle02_outcome = str(packet41_inputs.get("cycle02_outcome", ""))
    packet41_hold_state_changed = "PROMOTABLE" in packet41_cycle02_outcome or "REJECTED" in packet41_cycle02_outcome

    qm_criteria = qm.get("objective_quality", {}).get("criteria", {})
    qm_inputs = qm.get("objective_quality", {}).get("inputs", {})
    target_row_success_incremented = bool(qm_criteria.get("target_row_success_count_incremented", False))
    theorem_gap_delta_changed = bool(qm_criteria.get("theorem_gap_delta_changed", False))

    success_criteria = {
        "theorem_gap_decreased": theorem_gap_current < theorem_gap_prior,
        "seam_integration_gap_decreased": seam_gap_current < seam_gap_prior,
        "packet41_hold_state_changed": packet41_hold_state_changed,
        "packet41_rework_gap_reduced": bool(packet41_rework.get("success_criteria", {}).get("review_layer_clearance_gap_reduced", False)),
        "packet41_component_lift_observed": bool(packet41_component_lift.get("summary", {}).get("component_lift_observed", False)),
        "target_row_success_incremented": target_row_success_incremented,
        "theorem_gap_delta_changed": theorem_gap_delta_changed,
    }

    external_report_exists = False
    external_report_pointer = None
    if external_report_path:
        external_path = Path(external_report_path)
        if not external_path.is_absolute():
            external_path = REPO_ROOT / external_path
        external_report_exists = external_path.exists()
        external_report_pointer = _ptr(external_path)

    tranche_packet41 = {
        "target": "QFT_GR_PACKET41_SEAM_HOLD",
        "expected_blocker_state_change": "PACKET41_HOLD_TO_PROMOTABLE_OR_SUCCESSOR_DECISION",
        "success_threshold": "PACKET41_HOLD_STATE_CHANGED_OR_SUCCESSOR_PATH_NUMERICALLY_JUSTIFIED",
        "failure_diagnosis_rule": "HOLD_RETAINED_WITH_QUANTIFIED_NUMERIC_REASON",
        "evidence_bundle": {
            "packet41_report": _ptr(PACKET41_REPORT_PATH),
            "packet41_cycle02_outcome": packet41_cycle02_outcome,
        },
    }

    tranche_qm = {
        "target": "ROW-PILLAR-QM-001",
        "expected_blocker_state_change": "THEOREM_GAP_DELTA_NE_0_OR_TARGET_ROW_SUCCESS_INCREMENT",
        "success_threshold": "target_row_success_count_incremented_or_theorem_gap_delta_changed",
        "failure_diagnosis_rule": "explicit_failure_diagnosis_required",
        "evidence_bundle": {
            "qm_subtarget_report": _ptr(qm_path),
            "failure_diagnosis": qm_inputs.get("failure_diagnosis"),
        },
    }

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "mode": "SCIENCE_ONLY_EXECUTION",
        "freeze_rule": {
            "governance_expansion_frozen": True,
            "allowed_work_only": [
                "blocker_count_reduction",
                "row_success_increment",
                "numeric_clearance_analysis",
                "proof_or_evidence_discharge",
            ],
        },
        "tranches": {
            "packet41_strike": tranche_packet41,
            "packet41_numeric_rework": {
                "report_pointer": _ptr(PACKET41_REWORK_PATH),
                "actionable_parameter": packet41_rework.get("actionable_parameter", {}),
                "outcome": packet41_rework.get("summary", {}).get("outcome"),
            },
            "packet41_review_layer_decomposition": {
                "report_pointer": _ptr(PACKET41_DECOMP_PATH),
                "pass_count": packet41_decomp.get("decomposition", {}).get("pass_count"),
                "target_count": packet41_decomp.get("decomposition", {}).get("target_count"),
                "missing_components": packet41_decomp.get("decomposition", {}).get("missing_components", []),
            },
            "packet41_component_lift": {
                "report_pointer": _ptr(PACKET41_COMPONENT_LIFT_PATH),
                "target_component": packet41_component_lift.get("target_component"),
                "outcome": packet41_component_lift.get("summary", {}).get("outcome"),
                "component_lift_observed": packet41_component_lift.get("summary", {}).get("component_lift_observed"),
                "failure_diagnosis": packet41_component_lift.get("summary", {}).get("failure_diagnosis"),
                "narrow_followup_action": packet41_component_lift.get("summary", {}).get("narrow_followup_action"),
            },
            "packet41_retrospective_component_lift": (
                {
                    "report_pointer": _ptr(PACKET41_RETRO_COMPONENT_LIFT_PATH),
                    "target_component": packet41_retro_component_lift.get("target_component"),
                    "outcome": packet41_retro_component_lift.get("summary", {}).get("outcome"),
                    "component_lift_observed": packet41_retro_component_lift.get("summary", {}).get("component_lift_observed"),
                    "failure_diagnosis": packet41_retro_component_lift.get("summary", {}).get("failure_diagnosis"),
                    "narrow_followup_action": packet41_retro_component_lift.get("summary", {}).get("narrow_followup_action"),
                }
                if packet41_retro_component_lift is not None
                else None
            ),
            "packet41_branch_decision": (
                {
                    "report_pointer": _ptr(PACKET41_BRANCH_DECISION_PATH),
                    "decision": packet41_branch_decision.get("summary", {}).get("decision"),
                    "decision_reason": packet41_branch_decision.get("summary", {}).get("decision_reason"),
                    "next_action": packet41_branch_decision.get("summary", {}).get("next_action"),
                }
                if packet41_branch_decision is not None
                else None
            ),
            "post_packet41_reclassification_next_lane": (
                {
                    "report_pointer": _ptr(POST_PACKET41_RECLASSIFICATION_PATH),
                    "outcome": post_packet41_reclassification.get("summary", {}).get("outcome"),
                    "next_action": post_packet41_reclassification.get("summary", {}).get("next_action"),
                    "packet41_near_term_status": post_packet41_reclassification.get("packet41_reclassification", {}).get("near_term_blocker_burn_status"),
                    "next_active_lane": post_packet41_reclassification.get("next_active_lane"),
                }
                if post_packet41_reclassification is not None
                else None
            ),
            "qm_bounded_stop_rule_decision": (
                {
                    "report_pointer": _ptr(QM_BOUNDED_STOP_RULE_PATH),
                    "decision": qm_bounded_stop_rule.get("summary", {}).get("decision"),
                    "qm_continuation_earned": qm_bounded_stop_rule.get("summary", {}).get("qm_continuation_earned"),
                    "selected_narrow_subproblem": qm_bounded_stop_rule.get("summary", {}).get("selected_narrow_subproblem"),
                    "next_action": qm_bounded_stop_rule.get("summary", {}).get("next_action"),
                    "stop_rule_triggered": qm_bounded_stop_rule.get("summary", {}).get("stop_rule_triggered"),
                }
                if qm_bounded_stop_rule is not None
                else None
            ),
            "post_qm_reclassification_next_lane": (
                {
                    "report_pointer": _ptr(POST_QM_RECLASSIFICATION_PATH),
                    "outcome": post_qm_reclassification.get("summary", {}).get("outcome"),
                    "next_action": post_qm_reclassification.get("summary", {}).get("next_action"),
                    "qm_near_term_status": post_qm_reclassification.get("qm_reclassification", {}).get("near_term_blocker_burn_status"),
                    "next_active_lane": post_qm_reclassification.get("next_active_lane"),
                }
                if post_qm_reclassification is not None
                else None
            ),
            "gr_micro_subtarget": (
                {
                    "report_pointer": _ptr(GR_SUBTARGET_REPORT_PATH),
                    "phase_status": gr_subtarget.get("objective_quality", {}).get("summary", {}).get("phase_status"),
                    "theorem_gap_delta": gr_subtarget.get("objective_quality", {}).get("inputs", {}).get("theorem_gap_delta"),
                    "target_row_success_count": gr_subtarget.get("objective_quality", {}).get("inputs", {}).get("target_row_success_count"),
                    "next_action": gr_subtarget.get("objective_quality", {}).get("summary", {}).get("next_action"),
                }
                if gr_subtarget is not None
                else None
            ),
            "gr_bounded_stop_rule_decision": (
                {
                    "report_pointer": _ptr(GR_BOUNDED_STOP_RULE_PATH),
                    "decision": gr_bounded_stop_rule.get("summary", {}).get("decision"),
                    "gr_continuation_earned": gr_bounded_stop_rule.get("summary", {}).get("gr_continuation_earned"),
                    "stop_rule_triggered": gr_bounded_stop_rule.get("summary", {}).get("stop_rule_triggered"),
                    "next_action": gr_bounded_stop_rule.get("summary", {}).get("next_action"),
                    "selected_next_lane": gr_bounded_stop_rule.get("summary", {}).get("selected_next_lane"),
                }
                if gr_bounded_stop_rule is not None
                else None
            ),
            "stat_micro_subtarget": (
                {
                    "report_pointer": _ptr(STAT_SUBTARGET_REPORT_PATH),
                    "phase_status": stat_subtarget.get("objective_quality", {}).get("summary", {}).get("phase_status"),
                    "theorem_gap_delta": stat_subtarget.get("objective_quality", {}).get("inputs", {}).get("theorem_gap_delta"),
                    "target_row_success_count": stat_subtarget.get("objective_quality", {}).get("inputs", {}).get("target_row_success_count"),
                    "next_action": stat_subtarget.get("objective_quality", {}).get("summary", {}).get("next_action"),
                }
                if stat_subtarget is not None
                else None
            ),
            "stat_bounded_stop_rule_decision": (
                {
                    "report_pointer": _ptr(STAT_BOUNDED_STOP_RULE_PATH),
                    "decision": stat_bounded_stop_rule.get("summary", {}).get("decision"),
                    "stat_continuation_earned": stat_bounded_stop_rule.get("summary", {}).get("stat_continuation_earned"),
                    "stop_rule_triggered": stat_bounded_stop_rule.get("summary", {}).get("stop_rule_triggered"),
                    "next_action": stat_bounded_stop_rule.get("summary", {}).get("next_action"),
                    "selected_next_lane": stat_bounded_stop_rule.get("summary", {}).get("selected_next_lane"),
                }
                if stat_bounded_stop_rule is not None
                else None
            ),
            "cosmo_micro_subtarget": (
                {
                    "report_pointer": _ptr(COSMO_SUBTARGET_REPORT_PATH),
                    "phase_status": cosmo_subtarget.get("objective_quality", {}).get("summary", {}).get("phase_status"),
                    "theorem_gap_delta": cosmo_subtarget.get("objective_quality", {}).get("inputs", {}).get("theorem_gap_delta"),
                    "target_row_success_count": cosmo_subtarget.get("objective_quality", {}).get("inputs", {}).get("target_row_success_count"),
                    "next_action": cosmo_subtarget.get("objective_quality", {}).get("summary", {}).get("next_action"),
                }
                if cosmo_subtarget is not None
                else None
            ),
            "cosmo_bounded_stop_rule_decision": (
                {
                    "report_pointer": _ptr(COSMO_BOUNDED_STOP_RULE_PATH),
                    "decision": cosmo_bounded_stop_rule.get("summary", {}).get("decision"),
                    "cosmo_continuation_earned": cosmo_bounded_stop_rule.get("summary", {}).get("cosmo_continuation_earned"),
                    "stop_rule_triggered": cosmo_bounded_stop_rule.get("summary", {}).get("stop_rule_triggered"),
                    "next_action": cosmo_bounded_stop_rule.get("summary", {}).get("next_action"),
                    "higher_level_decision_required": cosmo_bounded_stop_rule.get("summary", {}).get("higher_level_decision_required"),
                }
                if cosmo_bounded_stop_rule is not None
                else None
            ),
            "science_attack_style_rethink_decision": (
                {
                    "report_pointer": _ptr(SCIENCE_ATTACK_STYLE_RETHINK_DECISION_PATH),
                    "decision": science_attack_style_rethink.get("summary", {}).get("decision"),
                    "all_five_lanes_flat": science_attack_style_rethink.get("summary", {}).get("all_five_lanes_flat"),
                    "selected_attack_class": science_attack_style_rethink.get("summary", {}).get("selected_attack_class"),
                    "next_action": science_attack_style_rethink.get("summary", {}).get("next_action"),
                }
                if science_attack_style_rethink is not None
                else None
            ),
            "simulation_first_falsification_packet": (
                {
                    "report_pointer": _ptr(SIMULATION_FIRST_PACKET_REPORT_PATH),
                    "packet_outcome": simulation_first_packet.get("summary", {}).get("packet_outcome"),
                    "scientific_state_change_observed": simulation_first_packet.get("summary", {}).get("scientific_state_change_observed"),
                    "blocker_facing_movement_observed": simulation_first_packet.get("summary", {}).get("blocker_facing_movement_observed"),
                    "next_action": simulation_first_packet.get("summary", {}).get("next_action"),
                }
                if simulation_first_packet is not None
                else None
            ),
            "simulation_first_falsification_campaign_decision": (
                {
                    "report_pointer": _ptr(SIMULATION_FIRST_CAMPAIGN_DECISION_PATH),
                    "decision": simulation_first_campaign_decision.get("summary", {}).get("decision"),
                    "packet_outcome": simulation_first_campaign_decision.get("summary", {}).get("packet_outcome"),
                    "scientific_state_change_observed": simulation_first_campaign_decision.get("summary", {}).get("scientific_state_change_observed"),
                    "next_action": simulation_first_campaign_decision.get("summary", {}).get("next_action"),
                }
                if simulation_first_campaign_decision is not None
                else None
            ),
            "simulation_first_falsification_packet_v1": (
                {
                    "report_pointer": _ptr(SIMULATION_FIRST_PACKET_V1_REPORT_PATH),
                    "packet_outcome": simulation_first_packet_v1.get("summary", {}).get("packet_outcome"),
                    "route_truly_nonviable": simulation_first_packet_v1.get("summary", {}).get("route_truly_nonviable"),
                    "route_narrower_regime": simulation_first_packet_v1.get("summary", {}).get("route_narrower_regime"),
                    "major_dead_end_elimination_observed": simulation_first_packet_v1.get("summary", {}).get("major_dead_end_elimination_observed"),
                    "blocker_facing_movement_observed": simulation_first_packet_v1.get("summary", {}).get("blocker_facing_movement_observed"),
                    "next_action": simulation_first_packet_v1.get("summary", {}).get("next_action"),
                }
                if simulation_first_packet_v1 is not None
                else None
            ),
            "simulation_first_falsification_campaign_decision_v1": (
                {
                    "report_pointer": _ptr(SIMULATION_FIRST_CAMPAIGN_V1_DECISION_PATH),
                    "decision": simulation_first_campaign_v1_decision.get("summary", {}).get("decision"),
                    "packet_outcome": simulation_first_campaign_v1_decision.get("summary", {}).get("packet_outcome"),
                    "major_dead_end_elimination_observed": simulation_first_campaign_v1_decision.get("summary", {}).get("major_dead_end_elimination_observed"),
                    "blocker_facing_movement_observed": simulation_first_campaign_v1_decision.get("summary", {}).get("blocker_facing_movement_observed"),
                    "next_action": simulation_first_campaign_v1_decision.get("summary", {}).get("next_action"),
                }
                if simulation_first_campaign_v1_decision is not None
                else None
            ),
            "simulation_first_falsification_packet_v2": (
                {
                    "report_pointer": _ptr(SIMULATION_FIRST_PACKET_V2_REPORT_PATH),
                    "packet_outcome": simulation_first_packet_v2.get("summary", {}).get("packet_outcome"),
                    "usable_boundary_mapped": simulation_first_packet_v2.get("summary", {}).get("usable_boundary_mapped"),
                    "condition_b_regime_limiter_confirmed": simulation_first_packet_v2.get("summary", {}).get("condition_b_regime_limiter_confirmed"),
                    "boundary_sharpness": simulation_first_packet_v2.get("summary", {}).get("boundary_sharpness"),
                    "blocker_facing_movement_observed": simulation_first_packet_v2.get("summary", {}).get("blocker_facing_movement_observed"),
                    "next_action": simulation_first_packet_v2.get("summary", {}).get("next_action"),
                }
                if simulation_first_packet_v2 is not None
                else None
            ),
            "simulation_first_falsification_campaign_decision_v2": (
                {
                    "report_pointer": _ptr(SIMULATION_FIRST_CAMPAIGN_V2_DECISION_PATH),
                    "decision": simulation_first_campaign_v2_decision.get("summary", {}).get("decision"),
                    "packet_outcome": simulation_first_campaign_v2_decision.get("summary", {}).get("packet_outcome"),
                    "usable_boundary_mapped": simulation_first_campaign_v2_decision.get("summary", {}).get("usable_boundary_mapped"),
                    "blocker_facing_movement_observed": simulation_first_campaign_v2_decision.get("summary", {}).get("blocker_facing_movement_observed"),
                    "next_action": simulation_first_campaign_v2_decision.get("summary", {}).get("next_action"),
                }
                if simulation_first_campaign_v2_decision is not None
                else None
            ),
            "simulation_first_falsification_packet_v3": (
                {
                    "report_pointer": _ptr(SIMULATION_FIRST_PACKET_V3_REPORT_PATH),
                    "packet_outcome": simulation_first_packet_v3.get("summary", {}).get("packet_outcome"),
                    "regime_precondition_met": simulation_first_packet_v3.get("summary", {}).get("regime_precondition_met"),
                    "condition_b_regime_limiter_confirmed": simulation_first_packet_v3.get("summary", {}).get("condition_b_regime_limiter_confirmed"),
                    "boundary_sharpness": simulation_first_packet_v3.get("summary", {}).get("boundary_sharpness"),
                    "theorem_gap_delta": simulation_first_packet_v3.get("summary", {}).get("theorem_gap_delta"),
                    "global_row_success_count": simulation_first_packet_v3.get("summary", {}).get("global_row_success_count"),
                    "named_blocker_class_changed_state": simulation_first_packet_v3.get("summary", {}).get("named_blocker_class_changed_state"),
                    "blocker_facing_movement_observed": simulation_first_packet_v3.get("summary", {}).get("blocker_facing_movement_observed"),
                    "next_action": simulation_first_packet_v3.get("summary", {}).get("next_action"),
                }
                if simulation_first_packet_v3 is not None
                else None
            ),
            "simulation_first_falsification_campaign_decision_v3": (
                {
                    "report_pointer": _ptr(SIMULATION_FIRST_CAMPAIGN_V3_DECISION_PATH),
                    "decision": simulation_first_campaign_v3_decision.get("summary", {}).get("decision"),
                    "packet_outcome": simulation_first_campaign_v3_decision.get("summary", {}).get("packet_outcome"),
                    "regime_precondition_met": simulation_first_campaign_v3_decision.get("summary", {}).get("regime_precondition_met"),
                    "blocker_facing_movement_observed": simulation_first_campaign_v3_decision.get("summary", {}).get("blocker_facing_movement_observed"),
                    "next_action": simulation_first_campaign_v3_decision.get("summary", {}).get("next_action"),
                }
                if simulation_first_campaign_v3_decision is not None
                else None
            ),
            "broader_seam_package_redesign_tranche": (
                {
                    "report_pointer": _ptr(BROADER_SEAM_REDESIGN_TRANCHE_REPORT_PATH),
                    "packet_outcome": broader_seam_redesign_tranche.get("summary", {}).get("packet_outcome"),
                    "target_seam_package": broader_seam_redesign_tranche.get("summary", {}).get("target_seam_package"),
                    "target_row_id": broader_seam_redesign_tranche.get("summary", {}).get("target_row_id"),
                    "structural_change_proposed": broader_seam_redesign_tranche.get("summary", {}).get("structural_change_proposed"),
                    "blocker_facing_movement_observed": broader_seam_redesign_tranche.get("summary", {}).get("blocker_facing_movement_observed"),
                    "seam_integration_gap_delta": broader_seam_redesign_tranche.get("summary", {}).get("seam_integration_gap_delta"),
                    "theorem_gap_delta": broader_seam_redesign_tranche.get("summary", {}).get("theorem_gap_delta"),
                    "global_row_success_count": broader_seam_redesign_tranche.get("summary", {}).get("global_row_success_count"),
                    "next_action": broader_seam_redesign_tranche.get("summary", {}).get("next_action"),
                }
                if broader_seam_redesign_tranche is not None
                else None
            ),
            "broader_seam_package_redesign_decision": (
                {
                    "report_pointer": _ptr(BROADER_SEAM_REDESIGN_DECISION_REPORT_PATH),
                    "decision": broader_seam_redesign_decision.get("summary", {}).get("decision"),
                    "packet_outcome": broader_seam_redesign_decision.get("summary", {}).get("packet_outcome"),
                    "blocker_facing_movement_observed": broader_seam_redesign_decision.get("summary", {}).get("blocker_facing_movement_observed"),
                    "next_action": broader_seam_redesign_decision.get("summary", {}).get("next_action"),
                }
                if broader_seam_redesign_decision is not None
                else None
            ),
            "external_discriminative_benchmark_packet": (
                {
                    "report_pointer": _ptr(EXTERNAL_BENCHMARK_PACKET_REPORT_PATH),
                    "packet_outcome": external_benchmark_packet.get("summary", {}).get("packet_outcome"),
                    "benchmark_id": external_benchmark_packet.get("summary", {}).get("benchmark_id"),
                    "route_structural_compatibility": external_benchmark_packet.get("summary", {}).get("route_structural_compatibility"),
                    "blocker_facing_movement_observed": external_benchmark_packet.get("summary", {}).get("blocker_facing_movement_observed"),
                    "decisive_route_elimination_observed": external_benchmark_packet.get("summary", {}).get("decisive_route_elimination_observed"),
                    "material_route_credibility_gain_observed": external_benchmark_packet.get("summary", {}).get("material_route_credibility_gain_observed"),
                    "theorem_gap_delta": external_benchmark_packet.get("summary", {}).get("theorem_gap_delta"),
                    "seam_integration_gap_delta": external_benchmark_packet.get("summary", {}).get("seam_integration_gap_delta"),
                    "global_row_success_count": external_benchmark_packet.get("summary", {}).get("global_row_success_count"),
                    "next_action": external_benchmark_packet.get("summary", {}).get("next_action"),
                }
                if external_benchmark_packet is not None
                else None
            ),
            "external_discriminative_benchmark_decision": (
                {
                    "report_pointer": _ptr(EXTERNAL_BENCHMARK_DECISION_REPORT_PATH),
                    "decision": external_benchmark_decision.get("summary", {}).get("decision"),
                    "packet_outcome": external_benchmark_decision.get("summary", {}).get("packet_outcome"),
                    "blocker_facing_movement_observed": external_benchmark_decision.get("summary", {}).get("blocker_facing_movement_observed"),
                    "decisive_route_elimination_observed": external_benchmark_decision.get("summary", {}).get("decisive_route_elimination_observed"),
                    "material_route_credibility_gain_observed": external_benchmark_decision.get("summary", {}).get("material_route_credibility_gain_observed"),
                    "next_action": external_benchmark_decision.get("summary", {}).get("next_action"),
                }
                if external_benchmark_decision is not None
                else None
            ),
            "fundamental_attack_strategy_rethink_packet": (
                {
                    "report_pointer": _ptr(FUNDAMENTAL_RETHINK_PACKET_REPORT_PATH),
                    "packet_outcome": fundamental_rethink_packet.get("summary", {}).get("packet_outcome"),
                    "all_current_attack_classes_nonproductive": fundamental_rethink_packet.get("summary", {}).get("all_current_attack_classes_nonproductive"),
                    "shared_failure_pattern": fundamental_rethink_packet.get("summary", {}).get("shared_failure_pattern"),
                    "redesigned_attack_hypothesis_id": fundamental_rethink_packet.get("summary", {}).get("redesigned_attack_hypothesis_id"),
                    "selected_next_experimental_class": fundamental_rethink_packet.get("summary", {}).get("selected_next_experimental_class"),
                    "blocker_facing_movement_observed": fundamental_rethink_packet.get("summary", {}).get("blocker_facing_movement_observed"),
                    "next_action": fundamental_rethink_packet.get("summary", {}).get("next_action"),
                }
                if fundamental_rethink_packet is not None
                else None
            ),
            "fundamental_attack_strategy_rethink_decision": (
                {
                    "report_pointer": _ptr(FUNDAMENTAL_RETHINK_DECISION_REPORT_PATH),
                    "decision": fundamental_rethink_decision.get("summary", {}).get("decision"),
                    "packet_outcome": fundamental_rethink_decision.get("summary", {}).get("packet_outcome"),
                    "selected_next_experimental_class": fundamental_rethink_decision.get("summary", {}).get("selected_next_experimental_class"),
                    "next_action": fundamental_rethink_decision.get("summary", {}).get("next_action"),
                }
                if fundamental_rethink_decision is not None
                else None
            ),
            "proof_debt_first_formal_campaign_packet": (
                {
                    "report_pointer": _ptr(PROOF_DEBT_FIRST_PACKET_REPORT_PATH),
                    "packet_outcome": proof_debt_first_packet.get("summary", {}).get("packet_outcome"),
                    "selected_cluster_id": proof_debt_first_packet.get("summary", {}).get("selected_cluster_id"),
                    "proof_debt_object_count": proof_debt_first_packet.get("summary", {}).get("proof_debt_object_count"),
                    "open_proof_debt_rows": proof_debt_first_packet.get("summary", {}).get("open_proof_debt_rows"),
                    "blocker_facing_movement_observed": proof_debt_first_packet.get("summary", {}).get("blocker_facing_movement_observed"),
                    "formal_gap_closed_tied_to_blocker": proof_debt_first_packet.get("summary", {}).get("formal_gap_closed_tied_to_blocker"),
                    "route_falsification_of_blocker_removal_path": proof_debt_first_packet.get("summary", {}).get("route_falsification_of_blocker_removal_path"),
                    "theorem_gap_delta": proof_debt_first_packet.get("summary", {}).get("theorem_gap_delta"),
                    "seam_integration_gap_delta": proof_debt_first_packet.get("summary", {}).get("seam_integration_gap_delta"),
                    "next_action": proof_debt_first_packet.get("summary", {}).get("next_action"),
                }
                if proof_debt_first_packet is not None
                else None
            ),
            "proof_debt_first_formal_campaign_decision": (
                {
                    "report_pointer": _ptr(PROOF_DEBT_FIRST_DECISION_REPORT_PATH),
                    "decision": proof_debt_first_decision.get("summary", {}).get("decision"),
                    "packet_outcome": proof_debt_first_decision.get("summary", {}).get("packet_outcome"),
                    "blocker_facing_movement_observed": proof_debt_first_decision.get("summary", {}).get("blocker_facing_movement_observed"),
                    "formal_gap_closed_tied_to_blocker": proof_debt_first_decision.get("summary", {}).get("formal_gap_closed_tied_to_blocker"),
                    "route_falsification_of_blocker_removal_path": proof_debt_first_decision.get("summary", {}).get("route_falsification_of_blocker_removal_path"),
                    "next_action": proof_debt_first_decision.get("summary", {}).get("next_action"),
                }
                if proof_debt_first_decision is not None
                else None
            ),
            "proof_debt_first_formal_campaign_discharge_tranche": (
                {
                    "report_pointer": _ptr(PROOF_DEBT_FIRST_DISCHARGE_TRANCHE_REPORT_PATH),
                    "tranche_state": proof_debt_first_discharge_tranche.get("summary", {}).get("tranche_state"),
                    "debt_object_count": proof_debt_first_discharge_tranche.get("summary", {}).get("debt_object_count"),
                    "any_object_discharged": proof_debt_first_discharge_tranche.get("summary", {}).get("any_object_discharged"),
                    "blocker_facing_movement_observed": proof_debt_first_discharge_tranche.get("summary", {}).get("blocker_facing_movement_observed"),
                    "formal_gap_closed_tied_to_blocker": proof_debt_first_discharge_tranche.get("summary", {}).get("formal_gap_closed_tied_to_blocker"),
                    "route_falsification_of_blocker_removal_path": proof_debt_first_discharge_tranche.get("summary", {}).get("route_falsification_of_blocker_removal_path"),
                    "theorem_gap_delta": proof_debt_first_discharge_tranche.get("summary", {}).get("theorem_gap_delta"),
                    "seam_integration_gap_delta": proof_debt_first_discharge_tranche.get("summary", {}).get("seam_integration_gap_delta"),
                    "global_row_success_count": proof_debt_first_discharge_tranche.get("summary", {}).get("global_row_success_count"),
                    "next_action": proof_debt_first_discharge_tranche.get("summary", {}).get("next_action"),
                }
                if proof_debt_first_discharge_tranche is not None
                else None
            ),
            "proof_debt_first_formal_campaign_discharge_decision": (
                {
                    "report_pointer": _ptr(PROOF_DEBT_FIRST_DISCHARGE_DECISION_REPORT_PATH),
                    "decision": proof_debt_first_discharge_decision.get("summary", {}).get("decision"),
                    "tranche_state": proof_debt_first_discharge_decision.get("summary", {}).get("tranche_state"),
                    "blocker_facing_movement_observed": proof_debt_first_discharge_decision.get("summary", {}).get("blocker_facing_movement_observed"),
                    "formal_gap_closed_tied_to_blocker": proof_debt_first_discharge_decision.get("summary", {}).get("formal_gap_closed_tied_to_blocker"),
                    "route_falsification_of_blocker_removal_path": proof_debt_first_discharge_decision.get("summary", {}).get("route_falsification_of_blocker_removal_path"),
                    "next_action": proof_debt_first_discharge_decision.get("summary", {}).get("next_action"),
                }
                if proof_debt_first_discharge_decision is not None
                else None
            ),
            "proof_debt_emu1_gate_surface_completion_tranche": (
                {
                    "report_pointer": _ptr(PROOF_DEBT_EMU1_GATE_COMPLETION_TRANCHE_REPORT_PATH),
                    "packet_outcome": proof_debt_emu1_gate_completion_tranche.get("summary", {}).get("packet_outcome"),
                    "gate_surface_exists": proof_debt_emu1_gate_completion_tranche.get("summary", {}).get("gate_surface_exists"),
                    "gate_surface_passes": proof_debt_emu1_gate_completion_tranche.get("summary", {}).get("gate_surface_passes"),
                    "rerun_ready": proof_debt_emu1_gate_completion_tranche.get("summary", {}).get("rerun_ready"),
                    "next_action": proof_debt_emu1_gate_completion_tranche.get("summary", {}).get("next_action"),
                }
                if proof_debt_emu1_gate_completion_tranche is not None
                else None
            ),
            "proof_debt_emu1_gate_surface_completion_decision": (
                {
                    "report_pointer": _ptr(PROOF_DEBT_EMU1_GATE_COMPLETION_DECISION_REPORT_PATH),
                    "decision": proof_debt_emu1_gate_completion_decision.get("summary", {}).get("decision"),
                    "packet_outcome": proof_debt_emu1_gate_completion_decision.get("summary", {}).get("packet_outcome"),
                    "next_action": proof_debt_emu1_gate_completion_decision.get("summary", {}).get("next_action"),
                }
                if proof_debt_emu1_gate_completion_decision is not None
                else None
            ),
            "proof_debt_cluster_branch_ruling": (
                {
                    "report_pointer": _ptr(PROOF_DEBT_CLUSTER_BRANCH_RULING_REPORT_PATH),
                    "branch_ruling": proof_debt_cluster_branch_ruling.get("summary", {}).get("branch_ruling"),
                    "allocation_decision": proof_debt_cluster_branch_ruling.get("summary", {}).get("allocation_decision"),
                    "retention_role": proof_debt_cluster_branch_ruling.get("summary", {}).get("retention_role"),
                    "rerun_policy": proof_debt_cluster_branch_ruling.get("summary", {}).get("rerun_policy"),
                    "blocker_facing_movement_observed": proof_debt_cluster_branch_ruling.get("summary", {}).get("blocker_facing_movement_observed"),
                    "theorem_gap_delta": proof_debt_cluster_branch_ruling.get("summary", {}).get("theorem_gap_delta"),
                    "seam_integration_gap_delta": proof_debt_cluster_branch_ruling.get("summary", {}).get("seam_integration_gap_delta"),
                    "global_row_success_count": proof_debt_cluster_branch_ruling.get("summary", {}).get("global_row_success_count"),
                    "next_action": proof_debt_cluster_branch_ruling.get("summary", {}).get("next_action"),
                }
                if proof_debt_cluster_branch_ruling is not None
                else None
            ),
            "proof_debt_next_cluster_selection": (
                {
                    "report_pointer": _ptr(PROOF_DEBT_NEXT_CLUSTER_SELECTION_REPORT_PATH),
                    "selection_outcome": proof_debt_next_cluster_selection.get("summary", {}).get("selection_outcome"),
                    "excluded_from_blocker_facing_priority": proof_debt_next_cluster_selection.get("summary", {}).get("excluded_from_blocker_facing_priority"),
                    "retained_support_lane": proof_debt_next_cluster_selection.get("summary", {}).get("retained_support_lane"),
                    "selected_next_cluster_id": proof_debt_next_cluster_selection.get("summary", {}).get("selected_next_cluster_id"),
                    "selected_next_cluster_name": proof_debt_next_cluster_selection.get("summary", {}).get("selected_next_cluster_name"),
                    "selected_next_cluster_leverage_score": proof_debt_next_cluster_selection.get("summary", {}).get("selected_next_cluster_leverage_score"),
                    "next_action": proof_debt_next_cluster_selection.get("summary", {}).get("next_action"),
                }
                if proof_debt_next_cluster_selection is not None
                else None
            ),
            "packet41_targeted_justification_evidence_injection": (
                {
                    "report_pointer": _ptr(PACKET41_TARGETED_EVIDENCE_PATH),
                    "outcome": targeted_evidence.get("summary", {}).get("outcome"),
                    "evidence_injection_ready": targeted_evidence.get("evidence_injection_ready"),
                }
                if targeted_evidence is not None
                else None
            ),
            "packet41_hold_fork_evidence_injection": (
                {
                    "report_pointer": _ptr(PACKET41_HOLD_FORK_EVIDENCE_PATH),
                    "outcome": hold_fork_evidence.get("summary", {}).get("outcome"),
                    "evidence_injection_ready": hold_fork_evidence.get("evidence_injection_ready"),
                }
                if hold_fork_evidence is not None
                else None
            ),
            "qm_micro_subtarget": tranche_qm,
        },
        "execution_path": {
            "packet41_first": True,
            "packet41_only": packet41_only,
            "packet41_component_target": packet41_component_target,
            "qm_fallback_executed": qm_fallback_executed,
        },
        "external_packet": {
            "requested": bool(external_report_path),
            "mode": external_packet_mode,
            "report_pointer": external_report_pointer,
            "report_exists": external_report_exists,
        },
        "success_criteria": success_criteria,
        "outcome_classification": _classify_outcome(success_criteria),
        "blocker_state_recompute": {
            "trend_pointer": _ptr(TREND_PATH),
            "ledger_pointer": _ptr(LEDGER_PATH),
            "science_baseline_pointer": _ptr(BASELINE_PATH),
            "theorem_gap_prior": theorem_gap_prior,
            "theorem_gap_current": theorem_gap_current,
            "seam_integration_gap_prior": seam_gap_prior,
            "seam_integration_gap_current": seam_gap_current,
            "progress_classification": ledger.get("progress_classification"),
            "global_next_action": baseline.get("completion_assessment", {}).get("global_next_action"),
        },
        "non_claim_boundary": "Repository-local science execution summary; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate science-mode strike summary.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "science_mode_strike_summary_20260411_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    parser.add_argument("--external-report-path", default=None)
    parser.add_argument("--external-packet-mode", default=None)
    parser.add_argument("--qm-fallback-executed", action="store_true")
    parser.add_argument("--packet41-only", action="store_true")
    parser.add_argument("--packet41-component-target", default="packet41_eligibility_review_pass")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_summary(
        captured_at_utc=ns.captured_at_utc,
        external_report_path=ns.external_report_path,
        external_packet_mode=ns.external_packet_mode,
        qm_fallback_executed=bool(ns.qm_fallback_executed),
        packet41_only=bool(ns.packet41_only),
        packet41_component_target=str(ns.packet41_component_target),
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"science_mode_strike_summary: outcome={payload['outcome_classification']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())