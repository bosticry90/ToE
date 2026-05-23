from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    BLOCKED_OBJECT,
    DEFAULT_CAPTURED_AT_UTC,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_004_CURRENT_BLOCKER,
    TRANCHE_004_DEPENDENCY,
    TRANCHE_004_FINDING_ID,
    TRANCHE_004_FUTURE_ROUTE,
    TRANCHE_004_RETAINED_REASON,
    TRANCHE_004_STATUS,
    TRANCHE_005_DEPENDENCY,
    TRANCHE_005_STATUS,
    TRANCHE_006_DEPENDENCY,
    TRANCHE_006_DEPENDENCY_CLASS,
    TRANCHE_006_FINDING_ID,
    TRANCHE_006_STATUS,
)
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_result_review_report import (
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    FORBIDDEN_EFFECTS as RESULT_REVIEW_FORBIDDEN_EFFECTS,
    NEXT_TARGET as EXPECTED_RESULT_REVIEW_SELECTED_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_release_readiness_adjudication_report import (
    RELEASE_READINESS_DECISION,
    SELECTED_TRANCHE_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_"
    "20260522_v0"
)
PACKET_ID = "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_v0"
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_"
    "PREPARED_WITH_NO_SOURCE_MAP_CLOSURE_OR_RELEASE_PROMOTION"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_20260522_v0.json"
)

NEXT_TARGET = (
    "review_v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_packet_result"
)
RESEARCH_EXECUTION_TARGET = (
    "execute_v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt"
)
POST_RESEARCH_REVIEW_TARGET = (
    "review_v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_result"
)
MAIN_PHYSICS_SELECTION_TARGET = "return_to_main_physics_target_selection_after_v01_alpha_release_hold"
RELEASE_HOLD_SUMMARY_TARGET = "prepare_release_hold_summary_and_pause_v01_alpha_assembly"
ASSEMBLE_RELEASE_PACKET_TARGET = "assemble_v01_alpha_release_packet"

RESEARCH_QUESTION = (
    "Can a bounded research-mode route identify a repo-local source-map witness chain "
    "for the retained QFT-GR source-map blocker without claiming closure, changing "
    "tranche 004 status, or reopening v0.1-alpha release assembly?"
)
RESEARCH_PACKET_MISSING_OBJECT = "source-map witness chain"

FORBIDDEN_EFFECTS = sorted(
    set(RESULT_REVIEW_FORBIDDEN_EFFECTS)
    | {
        "bounded_source_map_witness_chain_research_attempt_executed",
        "bounded_source_map_witness_chain_research_result_reviewed",
        "qft_gr_source_map_semantic_closure_claimed",
        "research_packet_treated_as_evidence_of_closure",
        "source_map_witness_chain_constructed",
        "source_map_witness_chain_research_execution_authorized",
    }
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _retained_tranche_004(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("retained_tranche_004_carry_forward", {}))


def _documented_rows(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("documented_dependency_nonblocking_tranches", []))


def _candidate_witness_chain_components() -> list[dict[str, str]]:
    return [
        {
            "component_id": "state_expectation_functional_semantics",
            "research_role": "define admissible state-to-expectation semantics",
            "packet_status": "candidate_only_not_constructed",
        },
        {
            "component_id": "renormalized_expectation_value_semantics",
            "research_role": "separate renormalized expectation semantics from supplied labels",
            "packet_status": "candidate_only_not_constructed",
        },
        {
            "component_id": "classical_source_admissibility_semantics",
            "research_role": "test whether the quantum expectation object can act as a classical source",
            "packet_status": "candidate_only_not_constructed",
        },
        {
            "component_id": "covariant_conservation_obligation",
            "research_role": "track conservation conditions required by the source map",
            "packet_status": "candidate_only_not_constructed",
        },
        {
            "component_id": "bianchi_compatibility_obligation",
            "research_role": "check compatibility with geometric conservation constraints",
            "packet_status": "candidate_only_not_constructed",
        },
        {
            "component_id": "einstein_coupling_obligation",
            "research_role": "identify any admissible coupling surface without asserting closure",
            "packet_status": "candidate_only_not_constructed",
        },
        {
            "component_id": "weak_curvature_source_identification",
            "research_role": "bound any weak-curvature source identification as a local subclaim only",
            "packet_status": "candidate_only_not_constructed",
        },
    ]


def _required_lean_theory_surfaces() -> list[dict[str, str]]:
    return [
        {
            "surface_id": "qft_gr_state_expectation_functional_semantics_surface",
            "required_object": "Lean/theory surface for admissible expectation-functional semantics.",
            "current_status": "required_future_research_surface",
        },
        {
            "surface_id": "qft_gr_renormalized_expectation_value_semantics_surface",
            "required_object": "Lean/theory surface for renormalized expectation-value semantics.",
            "current_status": "required_future_research_surface",
        },
        {
            "surface_id": "qft_gr_classical_source_admissibility_surface",
            "required_object": "Lean/theory surface for classical source admissibility.",
            "current_status": "required_future_research_surface",
        },
        {
            "surface_id": "qft_gr_covariant_conservation_surface",
            "required_object": "Lean/theory surface for covariant conservation obligations.",
            "current_status": "required_future_research_surface",
        },
        {
            "surface_id": "qft_gr_bianchi_compatibility_surface",
            "required_object": "Lean/theory surface for Bianchi compatibility obligations.",
            "current_status": "required_future_research_surface",
        },
        {
            "surface_id": "qft_gr_source_map_witness_chain_result_surface",
            "required_object": "Future result surface that accepts, rejects, or retains the witness-chain attempt.",
            "current_status": "required_future_review_surface",
        },
    ]


def _required_evidence_surfaces() -> list[dict[str, str]]:
    return [
        {
            "evidence_id": "source_map_ladder_dependency_trace",
            "required_evidence": "Trace from each ladder component to the source-map authorization question.",
            "current_status": "not_produced_by_this_packet",
        },
        {
            "evidence_id": "assumption_status_matrix",
            "required_evidence": "Matrix separating proved, supplied, missing, and retained assumptions.",
            "current_status": "not_produced_by_this_packet",
        },
        {
            "evidence_id": "semantic_transport_obligation_list",
            "required_evidence": "List of meaning-preservation obligations across QFT-GR source transport.",
            "current_status": "not_produced_by_this_packet",
        },
        {
            "evidence_id": "failure_mode_register",
            "required_evidence": "Register of exact reasons a witness-chain attempt may fail closed.",
            "current_status": "not_produced_by_this_packet",
        },
        {
            "evidence_id": "result_review_and_movement_plan",
            "required_evidence": "Future result-review and movement-registration plan before any status change.",
            "current_status": "not_produced_by_this_packet",
        },
        {
            "evidence_id": "pre_release_branch_health_requirement",
            "required_evidence": "Clean aggregate branch-health validation before any release-readiness claim.",
            "current_status": "not_run_by_this_packet",
        },
    ]


def _success_criteria() -> list[dict[str, str]]:
    return [
        {
            "criterion_id": "bounded_research_question_is_answerable",
            "criterion": "The future attempt states a precise witness-chain construction or refutation question.",
            "still_requires": "future_execution_and_result_review",
        },
        {
            "criterion_id": "all_required_components_have_status",
            "criterion": "Every candidate component receives a proved, supplied, missing, or refuted status.",
            "still_requires": "future_execution_and_result_review",
        },
        {
            "criterion_id": "closure_requires_governed_result_review",
            "criterion": "No source-map closure can be inferred before a governed result-review surface.",
            "still_requires": "future_result_review_and_possible_movement_registration",
        },
        {
            "criterion_id": "release_hold_survives_packet",
            "criterion": "The packet leaves release readiness held and assembly unauthorized.",
            "still_requires": "future_branch_health_before_any_release_claim",
        },
    ]


def _failure_criteria() -> list[dict[str, str]]:
    return [
        {
            "criterion_id": "candidate_component_missing",
            "condition": "Any required witness-chain component remains missing.",
            "required_result": "tranche_004_remains_retained_release_blocking",
        },
        {
            "criterion_id": "candidate_component_supplied_only",
            "condition": "Any required component remains supplied-only rather than repo-local.",
            "required_result": "source_map_closure_not_authorized",
        },
        {
            "criterion_id": "semantic_transport_unproven",
            "condition": "The route cannot preserve meaning from quantum expectation to classical source.",
            "required_result": "qft_gr_seam_remains_open",
        },
        {
            "criterion_id": "documentation_substituted_for_witness",
            "condition": "The route substitutes documentation for witness construction.",
            "required_result": "fail_closed_no_status_movement",
        },
        {
            "criterion_id": "release_readiness_reopened_early",
            "condition": "Release readiness or assembly is requested before tranche 004 resolution.",
            "required_result": "release_hold_continues",
        },
    ]


def _sandbox_research_mode_boundary() -> list[dict[str, str]]:
    return [
        {
            "boundary_id": "packet_preparation_only",
            "rule": "This packet prepares research-mode scope; it does not execute research.",
        },
        {
            "boundary_id": "release_lane_closed",
            "rule": "Release readiness remains held and release assembly remains unauthorized.",
        },
        {
            "boundary_id": "status_movement_requires_future_chain",
            "rule": "Any tranche 004 status movement requires future execution, review, and registration.",
        },
        {
            "boundary_id": "full_branch_health_deferred",
            "rule": "Full aggregate Lean branch health remains a later pre-release requirement.",
        },
    ]


def _promotion_firewall() -> list[dict[str, str]]:
    return [
        {"firewall_id": "no_release_readiness", "blocked_promotion": "v0.1-alpha readiness"},
        {"firewall_id": "no_release_assembly", "blocked_promotion": "release packet assembly"},
        {"firewall_id": "no_source_map_closure", "blocked_promotion": "source-map closure"},
        {"firewall_id": "no_qft_gr_seam_closure", "blocked_promotion": "QFT-GR seam closure"},
        {"firewall_id": "no_theorem_discharge", "blocked_promotion": "theorem/proof-debt discharge"},
        {"firewall_id": "no_phase2", "blocked_promotion": "Phase 2 authorization"},
        {"firewall_id": "no_empirical_validation", "blocked_promotion": "empirical validation"},
        {"firewall_id": "no_master_action_promotion", "blocked_promotion": "master-action promotion"},
    ]


def build_research_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    retained_tranche_004 = _retained_tranche_004(result_review)
    documented_rows = _documented_rows(result_review)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    candidate_next_targets = [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The bounded research packet must be result-reviewed before any research "
                "execution attempt is authorized."
            ),
        },
        {
            "target": RESEARCH_EXECUTION_TARGET,
            "decision": "deferred",
            "reason": "Research execution is not authorized by packet preparation.",
        },
        {
            "target": POST_RESEARCH_REVIEW_TARGET,
            "decision": "deferred",
            "reason": "Post-research review applies only after a future authorized execution attempt.",
        },
        {
            "target": MAIN_PHYSICS_SELECTION_TARGET,
            "decision": "deferred",
            "reason": "Broader target selection remains available after packet result review.",
        },
        {
            "target": RELEASE_HOLD_SUMMARY_TARGET,
            "decision": "deferred",
            "reason": "A release-hold pause summary remains available if research is declined.",
        },
        {
            "target": ASSEMBLE_RELEASE_PACKET_TARGET,
            "decision": "not_authorized",
            "reason": "Release assembly remains blocked by retained tranche 004.",
        },
    ]

    candidate_components = _candidate_witness_chain_components()
    lean_theory_surfaces = _required_lean_theory_surfaces()
    evidence_surfaces = _required_evidence_surfaces()
    success_criteria = _success_criteria()
    failure_criteria = _failure_criteria()
    sandbox_boundary = _sandbox_research_mode_boundary()
    promotion_firewall = _promotion_firewall()

    acceptance_criteria = {
        "consumes_expected_future_remediation_program_result_review": result_review.get(
            "review_id"
        )
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_schema_expected": result_review.get("schema_id")
        == EXPECTED_RESULT_REVIEW_SCHEMA_ID,
        "result_review_accepted": result_review.get("accepted") is True
        and result_review.get("future_remediation_program_accepted_as_planning_only") is True,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_selected_this_packet": result_review.get("selected_next_target")
        == EXPECTED_RESULT_REVIEW_SELECTED_TARGET,
        "result_review_authorized_packet_preparation": result_review.get(
            "bounded_source_map_witness_chain_research_packet_authorized_for_preparation"
        )
        is True
        and result_review.get("bounded_source_map_witness_chain_research_packet_prepared")
        is False,
        "blocked_object_preserved": result_review.get("blocked_object") == BLOCKED_OBJECT,
        "tranche_001_documented_nonblocking_preserved": result_review.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": result_review.get(
            "tranche_002_status"
        )
        == TRANCHE_002_STATUS,
        "tranche_003_documented_nonblocking_preserved": result_review.get(
            "tranche_003_status"
        )
        == TRANCHE_003_STATUS,
        "tranche_005_documented_nonblocking_preserved": result_review.get(
            "tranche_005_status"
        )
        == TRANCHE_005_STATUS
        and result_review.get("tranche_005_dependency") == TRANCHE_005_DEPENDENCY,
        "tranche_006_documented_nonblocking_preserved": result_review.get(
            "tranche_006_status"
        )
        == TRANCHE_006_STATUS
        and result_review.get("tranche_006_dependency") == TRANCHE_006_DEPENDENCY
        and result_review.get("tranche_006_dependency_class") == TRANCHE_006_DEPENDENCY_CLASS
        and result_review.get("tranche_006_dependency_finding_id") == TRANCHE_006_FINDING_ID,
        "documented_dependency_queue_count_expected": result_review.get(
            "documented_dependency_nonblocking_tranche_count"
        )
        == 5
        and [row.get("finding_id") for row in documented_rows]
        == [
            "V01-ALPHA-DEP-REM-001",
            "V01-ALPHA-DEP-REM-002",
            "V01-ALPHA-DEP-REM-003",
            "V01-ALPHA-DEP-REM-005",
            "V01-ALPHA-DEP-REM-006",
        ],
        "tranche_004_retained_blocker_preserved": result_review.get("tranche_004_status")
        == TRANCHE_004_STATUS
        and retained_tranche_004.get("status") == TRANCHE_004_STATUS
        and retained_tranche_004.get("dependency_finding_id") == TRANCHE_004_FINDING_ID
        and retained_tranche_004.get("dependency") == TRANCHE_004_DEPENDENCY
        and retained_tranche_004.get("current_blocker") == TRANCHE_004_CURRENT_BLOCKER
        and retained_tranche_004.get("retained_blocker_reason")
        == TRANCHE_004_RETAINED_REASON,
        "release_hold_preserved": result_review.get("release_readiness_decision_status")
        == RELEASE_READINESS_DECISION
        and result_review.get("release_readiness_held") is True
        and result_review.get("release_readiness_still_blocked") is True
        and result_review.get("release_readiness_proceed_authorized") is False,
        "release_assembly_remains_unauthorized": result_review.get(
            "release_assembly_authorized"
        )
        is False
        and result_review.get("release_packet_assembled") is False,
        "no_source_map_or_qft_gr_seam_closure": result_review.get(
            "source_map_closure_achieved"
        )
        is False
        and result_review.get("source_map_closure_claimed") is False
        and result_review.get("qft_gr_seam_closed") is False
        and result_review.get("qft_gr_seam_closure_claimed") is False,
        "no_theorem_or_proof_debt_discharge": result_review.get(
            "lean_theorem_debt_discharged"
        )
        is False
        and result_review.get("proof_debt_reduced") is False
        and result_review.get("retained_assumptions_discharged") is False,
        "no_phase2_empirical_or_master_action_promotion": result_review.get(
            "phase2_authorized"
        )
        is False
        and result_review.get("empirical_validation_authorized") is False
        and result_review.get("master_action_promotion_authorized") is False,
        "research_packet_sections_defined": len(candidate_components) == 7
        and len(lean_theory_surfaces) == 6
        and len(evidence_surfaces) == 6
        and len(success_criteria) == 4
        and len(failure_criteria) == 5
        and len(sandbox_boundary) == 4
        and len(promotion_firewall) == 8,
        "packet_prepares_only": RESEARCH_EXECUTION_TARGET
        != NEXT_TARGET
        and POST_RESEARCH_REVIEW_TARGET != NEXT_TARGET,
        "future_route_preserved": result_review.get("required_future_route_for_tranche_004")
        == TRANCHE_004_FUTURE_ROUTE,
        "forbidden_effects_all_false": all(
            value is False for value in forbidden_effect_status.values()
        ),
        "exactly_one_next_target_selected": sum(
            1 for row in candidate_next_targets if row["decision"] == "selected"
        )
        == 1,
        "selected_result_review_next": candidate_next_targets[0]["target"] == NEXT_TARGET,
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_BLOCKED",
        "consumes_future_remediation_program_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_future_remediation_program_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_future_remediation_program_result_review_schema_id": result_review.get(
            "schema_id"
        ),
        "packet_scope": (
            "PREPARE_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_ONLY_"
            "NO_RESEARCH_EXECUTION_SOURCE_MAP_CLOSURE_RELEASE_ASSEMBLY_OR_PROMOTION"
        ),
        "research_question": RESEARCH_QUESTION,
        "research_packet_prepared": accepted,
        "research_packet_prepared_only": accepted,
        "bounded_source_map_witness_chain_research_packet_prepared": accepted,
        "source_map_witness_chain_research_packet_prepared": accepted,
        "source_map_witness_chain_research_execution_authorized": False,
        "research_executed": False,
        "bounded_source_map_witness_chain_research_attempt_executed": False,
        "bounded_source_map_witness_chain_research_result_reviewed": False,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": TRANCHE_004_FINDING_ID,
        "selected_dependency": TRANCHE_004_DEPENDENCY,
        "selected_dependency_class": "blocked_bridge_authorization_dependency",
        "blocked_object": BLOCKED_OBJECT,
        "missing_object": RESEARCH_PACKET_MISSING_OBJECT,
        "carried_prior_missing_object": result_review.get("missing_object"),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_004_status": TRANCHE_004_STATUS,
        "tranche_005_status": TRANCHE_005_STATUS,
        "tranche_005_dependency": TRANCHE_005_DEPENDENCY,
        "tranche_006_status": TRANCHE_006_STATUS,
        "tranche_006_dependency": TRANCHE_006_DEPENDENCY,
        "tranche_006_dependency_class": TRANCHE_006_DEPENDENCY_CLASS,
        "tranche_006_dependency_finding_id": TRANCHE_006_FINDING_ID,
        "documented_dependency_nonblocking_tranches": documented_rows,
        "documented_dependency_nonblocking_tranche_count": len(documented_rows),
        "dependency_remediation_queue_exhausted": True,
        "simple_dependency_remediation_queue_exhausted": True,
        "retained_tranche_004_carry_forward": retained_tranche_004,
        "retained_release_blocking_obligations": result_review.get(
            "retained_release_blocking_obligations", []
        ),
        "retained_release_blocking_obligation_count": result_review.get(
            "retained_release_blocking_obligation_count"
        ),
        "release_readiness_decision_status": RELEASE_READINESS_DECISION,
        "release_readiness_held": True,
        "release_readiness_still_blocked": True,
        "release_readiness_blocked_by_tranche_004": True,
        "release_readiness_proceed_authorized": False,
        "current_release_posture": {
            "release_readiness": "held",
            "release_assembly": "unauthorized",
            "release_packet": "not_assembled",
            "public_release_completion": "not_authorized",
            "reason": RELEASE_READINESS_DECISION,
        },
        "candidate_witness_chain_components": candidate_components,
        "candidate_witness_chain_component_count": len(candidate_components),
        "required_lean_theory_surfaces": lean_theory_surfaces,
        "required_lean_theory_surface_count": len(lean_theory_surfaces),
        "required_evidence_surfaces": evidence_surfaces,
        "required_evidence_surface_count": len(evidence_surfaces),
        "success_criteria": success_criteria,
        "success_criteria_count": len(success_criteria),
        "failure_criteria": failure_criteria,
        "failure_criteria_count": len(failure_criteria),
        "sandbox_research_mode_boundary": sandbox_boundary,
        "sandbox_research_mode_boundary_count": len(sandbox_boundary),
        "promotion_firewall": promotion_firewall,
        "promotion_firewall_count": len(promotion_firewall),
        "post_packet_result_review_target": NEXT_TARGET,
        "future_research_execution_target": RESEARCH_EXECUTION_TARGET,
        "post_research_review_target": POST_RESEARCH_REVIEW_TARGET,
        "witness_chain_research_started": False,
        "witness_chain_constructed": False,
        "source_map_witness_chain_constructed": False,
        "source_map_research_executed_by_packet": False,
        "research_packet_treated_as_evidence_of_closure": False,
        "release_hold_summary_prepared": False,
        "main_physics_target_selection_returned": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "readiness_marking_authorized": False,
        "v01_alpha_marked_ready": False,
        "source_map_closure_achieved": False,
        "source_map_closure_claimed": False,
        "qft_gr_source_map_semantic_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "qft_gr_seam_closure_claimed": False,
        "phase2_authorized": False,
        "empirical_validation_authorized": False,
        "master_action_promotion_authorized": False,
        "tranche_004_future_route_required": result_review.get(
            "tranche_004_future_route_required"
        ),
        "required_future_route_for_tranche_004": TRANCHE_004_FUTURE_ROUTE,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "tranche_004_status_moved_by_packet": False,
        "tranche_004_status_downgraded": False,
        "tranche_004_retained_blocker_discharged": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "validation_claim_authorized": False,
        "forbidden_effect_status": forbidden_effect_status,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET",
        "selected_next_target_kind": "bounded_source_map_witness_chain_research_packet_result_review_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_ONLY_"
            "NO_RESEARCH_EXECUTION_SOURCE_MAP_CLOSURE_RELEASE_ASSEMBLY_OR_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained-tranche-004 bounded source-map witness-chain research packet "
            "prepares a research-mode investigation route only. It does not execute "
            "research, construct a witness chain, downgrade tranche 004, assemble release, "
            "mark readiness, discharge theorem/proof debt or retained assumptions, claim "
            "source-map or QFT-GR seam closure, authorize Phase 2, validate empirically, "
            "promote the master action, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_research_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_research_packet(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha retained tranche 004 bounded source-map "
            "witness-chain research packet."
        )
    )
    parser.add_argument("--result-review", type=Path, default=DEFAULT_RESULT_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    result_review_path = (
        ns.result_review
        if ns.result_review.is_absolute()
        else (REPO_ROOT / ns.result_review)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_research_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_packet_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
