from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_post_hold_routing_packet_due_to_retained_tranche_004_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_POST_HOLD_ROUTING_PACKET_PATH,
    NEXT_TARGET as EXPECTED_POST_HOLD_SELECTED_TARGET,
    OUTCOME_ID as EXPECTED_POST_HOLD_OUTCOME,
    PACKET_ID as EXPECTED_POST_HOLD_PACKET_ID,
    SCHEMA_ID as EXPECTED_POST_HOLD_SCHEMA_ID,
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
from formal.python.tools.v01_alpha_retained_tranche_004_release_readiness_adjudication_report import (
    RELEASE_READINESS_DECISION,
    SELECTED_TRANCHE_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_20260522_v0"
PROGRAM_ID = "V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_v0"
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_PREPARED_"
    "WITH_NO_SOURCE_MAP_CLOSURE_OR_RELEASE_PROMOTION"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_20260522_v0.json"
)

NEXT_TARGET = "review_v01_alpha_retained_tranche_004_future_remediation_program_result"
SOURCE_MAP_WITNESS_CHAIN_TARGET = (
    "prepare_v01_alpha_retained_tranche_004_source_map_witness_chain_continuation_packet"
)
MAIN_PHYSICS_SELECTION_TARGET = "return_to_main_physics_target_selection_after_release_hold"
RELEASE_HOLD_SUMMARY_TARGET = "prepare_release_hold_summary_and_pause_v01_alpha_assembly"
ASSEMBLE_RELEASE_PACKET_TARGET = "assemble_v01_alpha_release_packet"

PROGRAM_QUESTION = (
    "What future evidence, proof surfaces, documentation limits, failure conditions, "
    "success conditions, and lane boundaries are required before retained tranche 004 "
    "can be revisited?"
)

BLOCKED_OBJECT = "QFT-GR source-map semantic closure"
MISSING_OBJECT = "witness-chain construction"

FORBIDDEN_EFFECTS = [
    "axiom_spec_backed_debt_reduced",
    "claim_promotion_authorized",
    "empirical_validation_authorized",
    "future_remediation_program_executed",
    "lean_theorem_debt_discharged",
    "main_physics_target_selection_returned",
    "master_action_promotion_authorized",
    "phase2_authorized",
    "program_result_review_completed",
    "proof_debt_reduced",
    "qft_gr_seam_closed",
    "qft_gr_seam_closure_claimed",
    "readiness_marking_authorized",
    "release_assembly_authorized",
    "release_hold_summary_prepared",
    "release_packet_assembled",
    "retained_assumptions_discharged",
    "source_map_closure_achieved",
    "source_map_closure_claimed",
    "source_map_witness_chain_research_packet_prepared",
    "tranche_004_moved_to_documented_dependency_nonblocking",
    "tranche_004_retained_blocker_discharged",
    "tranche_004_status_downgraded",
    "v01_alpha_marked_ready",
    "witness_chain_constructed",
    "witness_chain_research_started",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _retained_tranche_004(packet: dict[str, Any]) -> dict[str, Any]:
    return dict(packet.get("retained_tranche_004_carry_forward", {}))


def _documented_rows(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return list(packet.get("documented_dependency_nonblocking_tranches", []))


def _evidence_requirements() -> list[dict[str, str]]:
    return [
        {
            "requirement_id": "repo_local_source_map_witness_chain_design",
            "required_object": (
                "A governed repo-local construction path for the QFT-GR source-map "
                "witness chain, not merely documentation or analogy."
            ),
            "current_status": "missing",
        },
        {
            "requirement_id": "semantic_bridge_authorization_criteria",
            "required_object": (
                "Explicit criteria showing when the source-map bridge is authorized "
                "rather than retained as a blocker."
            ),
            "current_status": "missing",
        },
        {
            "requirement_id": "obligation_ladder_satisfaction_evidence",
            "required_object": (
                "Repo-local evidence for the QFT-GR obligation ladder components "
                "needed by source-map closure."
            ),
            "current_status": "not_satisfied_by_this_program",
        },
        {
            "requirement_id": "result_review_and_movement_registration_chain",
            "required_object": (
                "Future result-review and movement-registration packets before any "
                "tranche 004 status change."
            ),
            "current_status": "future_governed_work_required",
        },
        {
            "requirement_id": "full_branch_health_before_release_readiness",
            "required_object": (
                "Clean pre-release validation, including full aggregate Lean branch "
                "health where required, before any readiness claim."
            ),
            "current_status": "not_run_by_this_program",
        },
    ]


def _proof_surface_requirements() -> list[dict[str, str]]:
    return [
        {
            "surface_id": "qft_gr_source_map_witness_chain_surface",
            "required_surface": (
                "A future Lean/proof surface that constructs, or formally refutes, "
                "the missing source-map witness-chain path."
            ),
            "current_status": "absent",
        },
        {
            "surface_id": "qft_gr_source_map_authorization_result_review",
            "required_surface": (
                "A result-review surface that accepts any witness-chain result without "
                "collapsing retained assumptions into closure by language alone."
            ),
            "current_status": "future_required",
        },
        {
            "surface_id": "release_status_movement_surface",
            "required_surface": (
                "A governed movement-registration surface if tranche 004 ever changes "
                "status."
            ),
            "current_status": "future_required",
        },
        {
            "surface_id": "qft_gr_ladder_guardrail_surface",
            "required_surface": (
                "Guardrail evidence preserving nonclosure whenever any ladder component "
                "remains supplied, missing, or merely documented."
            ),
            "current_status": "future_required",
        },
    ]


def _documentation_limits() -> list[dict[str, str]]:
    return [
        {
            "limit_id": "documentation_cannot_construct_witness",
            "limit": "Documentation cannot by itself construct the missing witness chain.",
        },
        {
            "limit_id": "documentation_cannot_authorize_source_map_closure",
            "limit": (
                "Documentation cannot authorize QFT-GR source-map closure without "
                "repo-local proof objects and governed result review."
            ),
        },
        {
            "limit_id": "documentation_cannot_move_tranche_004",
            "limit": (
                "Documentation cannot move tranche 004 from retained/release-blocking "
                "to documented/nonblocking."
            ),
        },
        {
            "limit_id": "documentation_cannot_reopen_release_assembly",
            "limit": (
                "Documentation cannot reopen v0.1-alpha release assembly while tranche "
                "004 remains retained."
            ),
        },
    ]


def _lane_classification() -> dict[str, Any]:
    return {
        "current_packet_lane": "release_control_plane",
        "substantive_future_work_lane": "bounded_qft_gr_source_map_research_mode",
        "release_lane_status": "held_until_tranche_004_has_governed_resolution_or_hold_continuation",
        "main_physics_target_selection_status": "deferred_until_program_result_review",
        "release_assembly_status": "not_authorized",
        "computational_physics_execution_status": "not_opened",
    }


def _failure_conditions() -> list[dict[str, str]]:
    return [
        {
            "condition_id": "witness_chain_absent",
            "condition": "No repo-local witness-chain construction is produced.",
            "required_result": "tranche_004_remains_retained_release_blocking",
        },
        {
            "condition_id": "closure_by_documentation_only",
            "condition": "The attempted route relies on documentation or restatement only.",
            "required_result": "fail_closed_no_status_movement",
        },
        {
            "condition_id": "ladder_component_missing_or_supplied_only",
            "condition": "A required source-map ladder component remains missing or supplied-only.",
            "required_result": "source_map_closure_not_authorized",
        },
        {
            "condition_id": "release_readiness_requested_before_resolution",
            "condition": "Release readiness or assembly is requested while tranche 004 remains retained.",
            "required_result": "release_hold_continues",
        },
    ]


def _success_conditions() -> list[dict[str, str]]:
    return [
        {
            "condition_id": "witness_chain_constructed_or_refuted",
            "condition": (
                "A governed repo-local proof surface constructs a source-map witness "
                "chain or records a precise refutation."
            ),
            "still_requires": "result_review_before_status_change",
        },
        {
            "condition_id": "authorization_criteria_satisfied",
            "condition": (
                "Source-map authorization criteria are explicitly satisfied by proof "
                "objects rather than rhetorical continuity."
            ),
            "still_requires": "movement_registration_before_release_readiness",
        },
        {
            "condition_id": "all_guardrails_remain_closed_until_review",
            "condition": (
                "No release assembly, readiness marking, seam closure, or master-action "
                "promotion occurs before governed review."
            ),
            "still_requires": "future_review_and_branch_health_validation",
        },
    ]


def build_future_remediation_program(
    *,
    post_hold_packet_path: Path = DEFAULT_POST_HOLD_ROUTING_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    post_hold_packet = _read_json(post_hold_packet_path)
    retained_tranche_004 = _retained_tranche_004(post_hold_packet)
    documented_rows = _documented_rows(post_hold_packet)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    routing_options = [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "A result review must accept or reject the prepared future remediation "
                "program before any lower-level witness-chain work is authorized."
            ),
        },
        {
            "target": SOURCE_MAP_WITNESS_CHAIN_TARGET,
            "decision": "deferred",
            "reason": (
                "Witness-chain work is substantive research-mode work and requires "
                "program result-review acceptance first."
            ),
        },
        {
            "target": MAIN_PHYSICS_SELECTION_TARGET,
            "decision": "deferred",
            "reason": (
                "Main physics target selection remains available after the release-hold "
                "program is reviewed."
            ),
        },
        {
            "target": RELEASE_HOLD_SUMMARY_TARGET,
            "decision": "deferred",
            "reason": (
                "A release-hold pause summary remains available after the remediation "
                "program is reviewed."
            ),
        },
        {
            "target": ASSEMBLE_RELEASE_PACKET_TARGET,
            "decision": "not_authorized",
            "reason": (
                "Release assembly remains blocked because tranche 004 is still retained "
                "and source-map closure is not authorized."
            ),
        },
    ]

    evidence_requirements = _evidence_requirements()
    proof_surface_requirements = _proof_surface_requirements()
    documentation_limits = _documentation_limits()
    failure_conditions = _failure_conditions()
    success_conditions = _success_conditions()
    lane_classification = _lane_classification()

    acceptance_criteria = {
        "consumes_expected_post_hold_routing_packet": post_hold_packet.get("packet_id")
        == EXPECTED_POST_HOLD_PACKET_ID,
        "post_hold_schema_expected": post_hold_packet.get("schema_id")
        == EXPECTED_POST_HOLD_SCHEMA_ID,
        "post_hold_packet_accepted": post_hold_packet.get("accepted") is True,
        "post_hold_outcome_expected": post_hold_packet.get("outcome_id")
        == EXPECTED_POST_HOLD_OUTCOME,
        "post_hold_selected_this_program": post_hold_packet.get("selected_next_target")
        == EXPECTED_POST_HOLD_SELECTED_TARGET,
        "post_hold_authorized_program_preparation": post_hold_packet.get(
            "future_remediation_program_authorized_for_preparation"
        )
        is True
        and post_hold_packet.get("future_remediation_program_prepared") is False,
        "tranche_001_documented_nonblocking_preserved": post_hold_packet.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": post_hold_packet.get(
            "tranche_002_status"
        )
        == TRANCHE_002_STATUS,
        "tranche_003_documented_nonblocking_preserved": post_hold_packet.get(
            "tranche_003_status"
        )
        == TRANCHE_003_STATUS,
        "tranche_005_documented_nonblocking_preserved": post_hold_packet.get(
            "tranche_005_status"
        )
        == TRANCHE_005_STATUS
        and post_hold_packet.get("tranche_005_dependency") == TRANCHE_005_DEPENDENCY,
        "tranche_006_documented_nonblocking_preserved": post_hold_packet.get(
            "tranche_006_status"
        )
        == TRANCHE_006_STATUS
        and post_hold_packet.get("tranche_006_dependency") == TRANCHE_006_DEPENDENCY
        and post_hold_packet.get("tranche_006_dependency_class") == TRANCHE_006_DEPENDENCY_CLASS
        and post_hold_packet.get("tranche_006_dependency_finding_id")
        == TRANCHE_006_FINDING_ID,
        "documented_dependency_queue_count_expected": post_hold_packet.get(
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
        "tranche_004_retained_blocker_preserved": post_hold_packet.get("tranche_004_status")
        == TRANCHE_004_STATUS
        and retained_tranche_004.get("status") == TRANCHE_004_STATUS
        and retained_tranche_004.get("dependency_finding_id") == TRANCHE_004_FINDING_ID
        and retained_tranche_004.get("dependency") == TRANCHE_004_DEPENDENCY
        and retained_tranche_004.get("current_blocker") == TRANCHE_004_CURRENT_BLOCKER
        and retained_tranche_004.get("retained_blocker_reason")
        == TRANCHE_004_RETAINED_REASON,
        "release_hold_preserved": post_hold_packet.get("release_readiness_decision_status")
        == RELEASE_READINESS_DECISION
        and post_hold_packet.get("release_readiness_held") is True
        and post_hold_packet.get("release_readiness_still_blocked") is True
        and post_hold_packet.get("release_readiness_proceed_authorized") is False,
        "release_assembly_remains_unauthorized": post_hold_packet.get(
            "release_assembly_authorized"
        )
        is False
        and post_hold_packet.get("release_packet_assembled") is False,
        "no_source_map_or_qft_gr_seam_closure": post_hold_packet.get(
            "source_map_closure_achieved"
        )
        is False
        and post_hold_packet.get("source_map_closure_claimed") is False
        and post_hold_packet.get("qft_gr_seam_closed") is False
        and post_hold_packet.get("qft_gr_seam_closure_claimed") is False,
        "no_theorem_or_proof_debt_discharge": post_hold_packet.get(
            "lean_theorem_debt_discharged"
        )
        is False
        and post_hold_packet.get("proof_debt_reduced") is False
        and post_hold_packet.get("retained_assumptions_discharged") is False,
        "no_phase2_empirical_or_master_action_promotion": post_hold_packet.get(
            "phase2_authorized"
        )
        is False
        and post_hold_packet.get("empirical_validation_authorized") is False
        and post_hold_packet.get("master_action_promotion_authorized") is False,
        "program_defines_required_evidence": len(evidence_requirements) == 5
        and all(row["current_status"] != "satisfied" for row in evidence_requirements),
        "program_defines_required_proof_surfaces": len(proof_surface_requirements) == 4,
        "program_defines_documentation_limits": len(documentation_limits) == 4,
        "program_defines_lane_classification": lane_classification["release_assembly_status"]
        == "not_authorized",
        "program_defines_failure_and_success_conditions": len(failure_conditions) == 4
        and len(success_conditions) == 3,
        "future_route_preserved": post_hold_packet.get("required_future_route_for_tranche_004")
        == TRANCHE_004_FUTURE_ROUTE,
        "forbidden_effects_all_false": all(
            value is False for value in forbidden_effect_status.values()
        ),
        "exactly_one_next_target_selected": sum(
            1 for row in routing_options if row["decision"] == "selected"
        )
        == 1,
        "selected_result_review_next": routing_options[0]["target"] == NEXT_TARGET,
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "program_id": PROGRAM_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_BLOCKED",
        "consumes_post_hold_routing_packet": EXPECTED_POST_HOLD_PACKET_ID,
        "consumes_post_hold_routing_packet_pointer": _ptr(post_hold_packet_path),
        "consumed_post_hold_routing_schema_id": post_hold_packet.get("schema_id"),
        "program_scope": (
            "PREPARE_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_ONLY_"
            "NO_SOURCE_MAP_CLOSURE_RELEASE_ASSEMBLY_READINESS_MARKING_OR_PROMOTION"
        ),
        "program_question": PROGRAM_QUESTION,
        "future_remediation_program_prepared": accepted,
        "future_remediation_program_executed": False,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": TRANCHE_004_FINDING_ID,
        "selected_dependency": TRANCHE_004_DEPENDENCY,
        "selected_dependency_class": "blocked_bridge_authorization_dependency",
        "blocked_object": BLOCKED_OBJECT,
        "missing_object": MISSING_OBJECT,
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
        "retained_release_blocking_obligations": post_hold_packet.get(
            "retained_release_blocking_obligations", []
        ),
        "retained_release_blocking_obligation_count": post_hold_packet.get(
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
        "evidence_required_before_revisiting_tranche_004": evidence_requirements,
        "proof_surfaces_required_before_status_movement": proof_surface_requirements,
        "documentation_alone_cannot_do": documentation_limits,
        "lane_classification": lane_classification,
        "failure_conditions": failure_conditions,
        "success_conditions": success_conditions,
        "source_map_witness_chain_research_packet_prepared": False,
        "witness_chain_research_started": False,
        "witness_chain_constructed": False,
        "release_hold_summary_prepared": False,
        "main_physics_target_selection_returned": False,
        "program_result_review_completed": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "readiness_marking_authorized": False,
        "v01_alpha_marked_ready": False,
        "source_map_closure_achieved": False,
        "source_map_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "qft_gr_seam_closure_claimed": False,
        "phase2_authorized": False,
        "empirical_validation_authorized": False,
        "master_action_promotion_authorized": False,
        "tranche_004_future_route_required": post_hold_packet.get(
            "tranche_004_future_route_required"
        ),
        "required_future_route_for_tranche_004": TRANCHE_004_FUTURE_ROUTE,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "tranche_004_status_downgraded": False,
        "tranche_004_retained_blocker_discharged": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "validation_claim_authorized": False,
        "forbidden_effect_status": forbidden_effect_status,
        "candidate_next_targets": routing_options,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM",
        "selected_next_target_kind": "future_remediation_program_result_review_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_ONLY_"
            "NO_SOURCE_MAP_RESEARCH_EXECUTION_RELEASE_ASSEMBLY_OR_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained-tranche-004 future remediation program defines future evidence, "
            "proof-surface, documentation-limit, lane, failure, and success conditions for "
            "the retained QFT-GR source-map blocker. It does not construct the witness "
            "chain, start source-map research, downgrade tranche 004, assemble release, "
            "mark readiness, discharge theorem/proof debt or retained assumptions, claim "
            "source-map or QFT-GR seam closure, authorize Phase 2, validate empirically, "
            "promote the master action, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_future_remediation_program(
    *,
    post_hold_packet_path: Path = DEFAULT_POST_HOLD_ROUTING_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_future_remediation_program(
        post_hold_packet_path=post_hold_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha retained tranche 004 future remediation program."
        )
    )
    parser.add_argument("--post-hold-packet", type=Path, default=DEFAULT_POST_HOLD_ROUTING_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    post_hold_packet_path = (
        ns.post_hold_packet
        if ns.post_hold_packet.is_absolute()
        else (REPO_ROOT / ns.post_hold_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_future_remediation_program(
        post_hold_packet_path=post_hold_packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_future_remediation_program_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
