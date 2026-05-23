from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_packet_report import (
    ASSEMBLE_RELEASE_PACKET_TARGET,
    BLOCKED_OBJECT,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_RESEARCH_PACKET_PATH,
    FORBIDDEN_EFFECTS as PACKET_FORBIDDEN_EFFECTS,
    MAIN_PHYSICS_SELECTION_TARGET,
    NEXT_TARGET as EXPECTED_PACKET_SELECTED_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_ID as EXPECTED_PACKET_ID,
    POST_RESEARCH_REVIEW_TARGET,
    RELEASE_HOLD_SUMMARY_TARGET,
    RESEARCH_EXECUTION_TARGET,
    RESEARCH_PACKET_MISSING_OBJECT,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
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
SCHEMA_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_RESULT_REVIEW_"
    "20260522_v0"
)
REVIEW_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_RESULT_REVIEW_"
    "ACCEPTS_RESEARCH_PACKET_AND_SELECTS_BOUNDED_NEXT_ACTION_ONLY"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_RESULT_REVIEW_20260522_v0.json"
)

NEXT_TARGET = RESEARCH_EXECUTION_TARGET
ROUTE_TO_RESEARCH_MODE_TARGET = (
    "route_v01_alpha_tranche_004_to_research_mode_or_main_physics_target_selection"
)

FORBIDDEN_EFFECTS = sorted(
    (set(PACKET_FORBIDDEN_EFFECTS) - {"source_map_witness_chain_research_execution_authorized"})
    | {
        "bounded_source_map_witness_chain_research_attempt_executed",
        "bounded_source_map_witness_chain_research_result_reviewed",
        "packet_accepted_as_closure_evidence",
        "qft_gr_source_map_semantic_closure_claimed",
        "release_assembly_authorized_by_review",
        "source_map_research_executed_by_review",
        "source_map_witness_chain_constructed",
        "tranche_004_status_moved_by_review",
    }
)


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


def build_result_review(
    *,
    packet_path: Path = DEFAULT_RESEARCH_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    retained_tranche_004 = _retained_tranche_004(packet)
    documented_rows = _documented_rows(packet)
    packet_forbidden = dict(packet.get("forbidden_effect_status", {}))
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    candidate_next_targets = [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The prepared packet defines a bounded executable research attempt, so "
                "the result review selects execution as the only next action while "
                "preserving all nonclosure guardrails."
            ),
        },
        {
            "target": ROUTE_TO_RESEARCH_MODE_TARGET,
            "decision": "deferred",
            "reason": (
                "Routing away from execution remains available if the execution packet "
                "is later rejected or paused."
            ),
        },
        {
            "target": POST_RESEARCH_REVIEW_TARGET,
            "decision": "deferred",
            "reason": "Post-research review applies only after a future execution attempt.",
        },
        {
            "target": MAIN_PHYSICS_SELECTION_TARGET,
            "decision": "deferred",
            "reason": "Broader target selection remains available after the bounded attempt path.",
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

    candidate_components = list(packet.get("candidate_witness_chain_components", []))
    lean_theory_surfaces = list(packet.get("required_lean_theory_surfaces", []))
    evidence_surfaces = list(packet.get("required_evidence_surfaces", []))
    success_criteria = list(packet.get("success_criteria", []))
    failure_criteria = list(packet.get("failure_criteria", []))
    sandbox_boundary = list(packet.get("sandbox_research_mode_boundary", []))
    promotion_firewall = list(packet.get("promotion_firewall", []))

    acceptance_criteria = {
        "consumes_expected_research_packet": packet.get("packet_id") == EXPECTED_PACKET_ID,
        "packet_schema_expected": packet.get("schema_id") == EXPECTED_PACKET_SCHEMA_ID,
        "packet_prepared_and_accepted": packet.get("prepared") is True
        and packet.get("accepted") is True
        and packet.get("research_packet_prepared_only") is True,
        "packet_outcome_expected": packet.get("outcome_id") == EXPECTED_PACKET_OUTCOME,
        "packet_selected_this_review": packet.get("selected_next_target")
        == EXPECTED_PACKET_SELECTED_TARGET,
        "packet_defined_executable_attempt": packet.get("future_research_execution_target")
        == RESEARCH_EXECUTION_TARGET
        and packet.get("source_map_witness_chain_research_execution_authorized") is False
        and packet.get("research_executed") is False,
        "blocked_and_missing_objects_preserved": packet.get("blocked_object") == BLOCKED_OBJECT
        and packet.get("missing_object") == RESEARCH_PACKET_MISSING_OBJECT,
        "tranche_001_documented_nonblocking_preserved": packet.get("tranche_001_status")
        == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": packet.get("tranche_002_status")
        == TRANCHE_002_STATUS,
        "tranche_003_documented_nonblocking_preserved": packet.get("tranche_003_status")
        == TRANCHE_003_STATUS,
        "tranche_005_documented_nonblocking_preserved": packet.get("tranche_005_status")
        == TRANCHE_005_STATUS
        and packet.get("tranche_005_dependency") == TRANCHE_005_DEPENDENCY,
        "tranche_006_documented_nonblocking_preserved": packet.get("tranche_006_status")
        == TRANCHE_006_STATUS
        and packet.get("tranche_006_dependency") == TRANCHE_006_DEPENDENCY
        and packet.get("tranche_006_dependency_class") == TRANCHE_006_DEPENDENCY_CLASS
        and packet.get("tranche_006_dependency_finding_id") == TRANCHE_006_FINDING_ID,
        "documented_dependency_queue_count_expected": packet.get(
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
        "tranche_004_retained_blocker_preserved": packet.get("tranche_004_status")
        == TRANCHE_004_STATUS
        and retained_tranche_004.get("status") == TRANCHE_004_STATUS
        and retained_tranche_004.get("dependency_finding_id") == TRANCHE_004_FINDING_ID
        and retained_tranche_004.get("dependency") == TRANCHE_004_DEPENDENCY
        and retained_tranche_004.get("current_blocker") == TRANCHE_004_CURRENT_BLOCKER
        and retained_tranche_004.get("retained_blocker_reason")
        == TRANCHE_004_RETAINED_REASON,
        "release_hold_preserved": packet.get("release_readiness_decision_status")
        == RELEASE_READINESS_DECISION
        and packet.get("release_readiness_held") is True
        and packet.get("release_readiness_still_blocked") is True
        and packet.get("release_readiness_proceed_authorized") is False,
        "release_assembly_remains_unauthorized": packet.get("release_assembly_authorized")
        is False
        and packet.get("release_packet_assembled") is False,
        "no_source_map_or_qft_gr_seam_closure": packet.get("source_map_closure_achieved")
        is False
        and packet.get("source_map_closure_claimed") is False
        and packet.get("qft_gr_seam_closed") is False
        and packet.get("qft_gr_seam_closure_claimed") is False,
        "no_theorem_or_proof_debt_discharge": packet.get("lean_theorem_debt_discharged")
        is False
        and packet.get("proof_debt_reduced") is False
        and packet.get("retained_assumptions_discharged") is False,
        "no_phase2_empirical_or_master_action_promotion": packet.get("phase2_authorized")
        is False
        and packet.get("empirical_validation_authorized") is False
        and packet.get("master_action_promotion_authorized") is False,
        "research_packet_sections_carried": len(candidate_components) == 7
        and len(lean_theory_surfaces) == 6
        and len(evidence_surfaces) == 6
        and len(success_criteria) == 4
        and len(failure_criteria) == 5
        and len(sandbox_boundary) == 4
        and len(promotion_firewall) == 8,
        "future_route_preserved": packet.get("required_future_route_for_tranche_004")
        == TRANCHE_004_FUTURE_ROUTE,
        "review_does_not_execute_research": NEXT_TARGET == RESEARCH_EXECUTION_TARGET
        and packet.get("bounded_source_map_witness_chain_research_attempt_executed")
        is False,
        "forbidden_effects_all_false": all(
            value is False for value in forbidden_effect_status.values()
        )
        and all(packet_forbidden.get(key, False) is False for key in packet_forbidden),
        "exactly_one_next_target_selected": sum(
            1 for row in candidate_next_targets if row["decision"] == "selected"
        )
        == 1,
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_RESULT_REVIEW_BLOCKED",
        "consumes_bounded_source_map_witness_chain_research_packet": EXPECTED_PACKET_ID,
        "consumes_bounded_source_map_witness_chain_research_packet_pointer": _ptr(
            packet_path
        ),
        "consumed_bounded_source_map_witness_chain_research_packet_schema_id": packet.get(
            "schema_id"
        ),
        "review_scope": (
            "REVIEW_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_ONLY_"
            "AUTHORIZE_NEXT_EXECUTION_TARGET_NO_RESEARCH_EXECUTION_SOURCE_MAP_CLOSURE_OR_PROMOTION"
        ),
        "research_packet_reviewed": True,
        "research_packet_accepted": accepted,
        "research_packet_accepted_as_preparation_only": accepted,
        "packet_accepted_as_closure_evidence": False,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": TRANCHE_004_FINDING_ID,
        "selected_dependency": TRANCHE_004_DEPENDENCY,
        "selected_dependency_class": "blocked_bridge_authorization_dependency",
        "blocked_object": BLOCKED_OBJECT,
        "missing_object": RESEARCH_PACKET_MISSING_OBJECT,
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
        "retained_release_blocking_obligations": packet.get(
            "retained_release_blocking_obligations", []
        ),
        "retained_release_blocking_obligation_count": packet.get(
            "retained_release_blocking_obligation_count"
        ),
        "release_readiness_decision_status": RELEASE_READINESS_DECISION,
        "release_readiness_held": True,
        "release_readiness_still_blocked": True,
        "release_readiness_blocked_by_tranche_004": True,
        "release_readiness_proceed_authorized": False,
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
        "bounded_source_map_witness_chain_research_attempt_authorized_for_execution": accepted,
        "source_map_witness_chain_research_execution_authorized": accepted,
        "bounded_source_map_witness_chain_research_attempt_executed": False,
        "source_map_research_executed_by_review": False,
        "research_executed": False,
        "bounded_source_map_witness_chain_research_result_reviewed": False,
        "witness_chain_research_started": False,
        "witness_chain_constructed": False,
        "source_map_witness_chain_constructed": False,
        "release_hold_summary_prepared": False,
        "main_physics_target_selection_returned": False,
        "release_assembly_authorized": False,
        "release_assembly_authorized_by_review": False,
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
        "tranche_004_future_route_required": packet.get("tranche_004_future_route_required"),
        "required_future_route_for_tranche_004": TRANCHE_004_FUTURE_ROUTE,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "tranche_004_status_moved_by_review": False,
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
        else "REMEDIATE_V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_RESULT_REVIEW",
        "selected_next_target_kind": "bounded_source_map_witness_chain_research_attempt_execution_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "EXECUTE_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_ONLY_"
            "NO_SOURCE_MAP_CLOSURE_RELEASE_ASSEMBLY_OR_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained-tranche-004 bounded source-map witness-chain research packet "
            "result review accepts the packet as preparation only and selects one bounded "
            "execution target. It does not execute research, construct a witness chain, "
            "downgrade tranche 004, assemble release, mark readiness, discharge theorem/"
            "proof debt or retained assumptions, claim source-map or QFT-GR seam closure, "
            "authorize Phase 2, validate empirically, promote the master action, or make "
            "an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_result_review(
    *,
    packet_path: Path = DEFAULT_RESEARCH_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(packet_path=packet_path, captured_at_utc=captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha retained tranche 004 bounded source-map "
            "witness-chain research packet result review."
        )
    )
    parser.add_argument("--packet", type=Path, default=DEFAULT_RESEARCH_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_packet_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
