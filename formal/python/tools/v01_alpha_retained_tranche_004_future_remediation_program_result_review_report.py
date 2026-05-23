from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    BLOCKED_OBJECT,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_PROGRAM_PATH,
    FORBIDDEN_EFFECTS as PROGRAM_FORBIDDEN_EFFECTS,
    MISSING_OBJECT,
    NEXT_TARGET as EXPECTED_PROGRAM_SELECTED_TARGET,
    OUTCOME_ID as EXPECTED_PROGRAM_OUTCOME,
    PROGRAM_ID as EXPECTED_PROGRAM_ID,
    SCHEMA_ID as EXPECTED_PROGRAM_SCHEMA_ID,
    SOURCE_MAP_WITNESS_CHAIN_TARGET as PROGRAM_SOURCE_MAP_WITNESS_CHAIN_TARGET,
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
    "V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_RESULT_REVIEW_"
    "20260522_v0"
)
REVIEW_ID = "V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_RESULT_REVIEW_"
    "ACCEPTS_REMEDIATION_PROGRAM_AND_SELECTS_NEXT_BOUNDED_ROUTE_ONLY"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_RESULT_REVIEW_20260522_v0.json"
)

NEXT_TARGET = (
    "prepare_v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_packet"
)
MAIN_PHYSICS_SELECTION_TARGET = "return_to_main_physics_target_selection_after_v01_alpha_release_hold"
RELEASE_HOLD_SUMMARY_TARGET = "prepare_release_hold_summary_and_pause_v01_alpha_assembly"
ASSEMBLE_RELEASE_PACKET_TARGET = "assemble_v01_alpha_release_packet"

FORBIDDEN_EFFECTS = sorted(
    set(PROGRAM_FORBIDDEN_EFFECTS)
    | {
        "bounded_source_map_witness_chain_research_packet_prepared",
        "program_accepted_as_closure_evidence",
        "release_assembly_authorized_by_review",
        "source_map_research_executed_by_review",
        "tranche_004_status_moved_by_review",
    }
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _retained_tranche_004(program: dict[str, Any]) -> dict[str, Any]:
    return dict(program.get("retained_tranche_004_carry_forward", {}))


def _documented_rows(program: dict[str, Any]) -> list[dict[str, Any]]:
    return list(program.get("documented_dependency_nonblocking_tranches", []))


def build_result_review(
    *,
    program_path: Path = DEFAULT_PROGRAM_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    program = _read_json(program_path)
    retained_tranche_004 = _retained_tranche_004(program)
    documented_rows = _documented_rows(program)
    program_forbidden = dict(program.get("forbidden_effect_status", {}))
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    candidate_next_targets = [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The remediation program is accepted as planning-only, so the next "
                "bounded route may prepare, but not execute, a source-map witness-chain "
                "research packet for retained tranche 004."
            ),
        },
        {
            "target": MAIN_PHYSICS_SELECTION_TARGET,
            "decision": "deferred",
            "reason": (
                "Returning to broader physics target selection remains available if the "
                "bounded witness-chain packet is rejected or paused later."
            ),
        },
        {
            "target": PROGRAM_SOURCE_MAP_WITNESS_CHAIN_TARGET,
            "decision": "superseded_by_selected_refinement",
            "reason": (
                "The program's generic continuation-packet route is refined into the "
                "explicit bounded source-map witness-chain research packet target."
            ),
        },
        {
            "target": RELEASE_HOLD_SUMMARY_TARGET,
            "decision": "deferred",
            "reason": (
                "A release-hold pause summary remains available after the selected route "
                "is reviewed or declined."
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

    evidence_requirements = list(program.get("evidence_required_before_revisiting_tranche_004", []))
    proof_surface_requirements = list(
        program.get("proof_surfaces_required_before_status_movement", [])
    )
    documentation_limits = list(program.get("documentation_alone_cannot_do", []))
    failure_conditions = list(program.get("failure_conditions", []))
    success_conditions = list(program.get("success_conditions", []))
    lane_classification = dict(program.get("lane_classification", {}))

    acceptance_criteria = {
        "consumes_expected_program": program.get("program_id") == EXPECTED_PROGRAM_ID,
        "program_schema_expected": program.get("schema_id") == EXPECTED_PROGRAM_SCHEMA_ID,
        "program_prepared_and_accepted": program.get("prepared") is True
        and program.get("accepted") is True
        and program.get("future_remediation_program_prepared") is True,
        "program_outcome_expected": program.get("outcome_id") == EXPECTED_PROGRAM_OUTCOME,
        "program_selected_this_review": program.get("selected_next_target")
        == EXPECTED_PROGRAM_SELECTED_TARGET,
        "program_scope_is_planning_only": program.get("future_remediation_program_executed")
        is False
        and program.get("program_result_review_completed") is False,
        "blocked_and_missing_objects_preserved": program.get("blocked_object") == BLOCKED_OBJECT
        and program.get("missing_object") == MISSING_OBJECT,
        "tranche_001_documented_nonblocking_preserved": program.get("tranche_001_status")
        == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": program.get("tranche_002_status")
        == TRANCHE_002_STATUS,
        "tranche_003_documented_nonblocking_preserved": program.get("tranche_003_status")
        == TRANCHE_003_STATUS,
        "tranche_005_documented_nonblocking_preserved": program.get("tranche_005_status")
        == TRANCHE_005_STATUS
        and program.get("tranche_005_dependency") == TRANCHE_005_DEPENDENCY,
        "tranche_006_documented_nonblocking_preserved": program.get("tranche_006_status")
        == TRANCHE_006_STATUS
        and program.get("tranche_006_dependency") == TRANCHE_006_DEPENDENCY
        and program.get("tranche_006_dependency_class") == TRANCHE_006_DEPENDENCY_CLASS
        and program.get("tranche_006_dependency_finding_id") == TRANCHE_006_FINDING_ID,
        "documented_dependency_queue_count_expected": program.get(
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
        "tranche_004_retained_blocker_preserved": program.get("tranche_004_status")
        == TRANCHE_004_STATUS
        and retained_tranche_004.get("status") == TRANCHE_004_STATUS
        and retained_tranche_004.get("dependency_finding_id") == TRANCHE_004_FINDING_ID
        and retained_tranche_004.get("dependency") == TRANCHE_004_DEPENDENCY
        and retained_tranche_004.get("current_blocker") == TRANCHE_004_CURRENT_BLOCKER
        and retained_tranche_004.get("retained_blocker_reason")
        == TRANCHE_004_RETAINED_REASON,
        "release_hold_preserved": program.get("release_readiness_decision_status")
        == RELEASE_READINESS_DECISION
        and program.get("release_readiness_held") is True
        and program.get("release_readiness_still_blocked") is True
        and program.get("release_readiness_proceed_authorized") is False,
        "release_assembly_remains_unauthorized": program.get("release_assembly_authorized")
        is False
        and program.get("release_packet_assembled") is False,
        "no_source_map_or_qft_gr_seam_closure": program.get("source_map_closure_achieved")
        is False
        and program.get("source_map_closure_claimed") is False
        and program.get("qft_gr_seam_closed") is False
        and program.get("qft_gr_seam_closure_claimed") is False,
        "no_theorem_or_proof_debt_discharge": program.get("lean_theorem_debt_discharged")
        is False
        and program.get("proof_debt_reduced") is False
        and program.get("retained_assumptions_discharged") is False,
        "no_phase2_empirical_or_master_action_promotion": program.get("phase2_authorized")
        is False
        and program.get("empirical_validation_authorized") is False
        and program.get("master_action_promotion_authorized") is False,
        "program_requirements_carried": len(evidence_requirements) == 5
        and len(proof_surface_requirements) == 4
        and len(documentation_limits) == 4
        and len(failure_conditions) == 4
        and len(success_conditions) == 3
        and lane_classification.get("release_assembly_status") == "not_authorized",
        "future_route_preserved": program.get("required_future_route_for_tranche_004")
        == TRANCHE_004_FUTURE_ROUTE,
        "selected_bounded_witness_chain_packet_preparation": NEXT_TARGET
        == "prepare_v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_packet",
        "forbidden_effects_all_false": all(
            value is False for value in forbidden_effect_status.values()
        )
        and all(program_forbidden.get(key, False) is False for key in program_forbidden),
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
        else "V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_RESULT_REVIEW_BLOCKED",
        "consumes_future_remediation_program": EXPECTED_PROGRAM_ID,
        "consumes_future_remediation_program_pointer": _ptr(program_path),
        "consumed_future_remediation_program_schema_id": program.get("schema_id"),
        "review_scope": (
            "REVIEW_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_ONLY_"
            "ACCEPT_PLANNING_SELECT_NEXT_BOUNDED_ROUTE_NO_SOURCE_MAP_CLOSURE_OR_PROMOTION"
        ),
        "future_remediation_program_reviewed": True,
        "future_remediation_program_accepted": accepted,
        "future_remediation_program_accepted_as_planning_only": accepted,
        "program_accepted_as_closure_evidence": False,
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
        "retained_release_blocking_obligations": program.get(
            "retained_release_blocking_obligations", []
        ),
        "retained_release_blocking_obligation_count": program.get(
            "retained_release_blocking_obligation_count"
        ),
        "release_readiness_decision_status": RELEASE_READINESS_DECISION,
        "release_readiness_held": True,
        "release_readiness_still_blocked": True,
        "release_readiness_blocked_by_tranche_004": True,
        "release_readiness_proceed_authorized": False,
        "evidence_required_before_revisiting_tranche_004": evidence_requirements,
        "proof_surfaces_required_before_status_movement": proof_surface_requirements,
        "documentation_alone_cannot_do": documentation_limits,
        "lane_classification": lane_classification,
        "failure_conditions": failure_conditions,
        "success_conditions": success_conditions,
        "bounded_source_map_witness_chain_research_packet_authorized_for_preparation": accepted,
        "bounded_source_map_witness_chain_research_packet_prepared": False,
        "source_map_witness_chain_research_packet_prepared": False,
        "source_map_research_executed_by_review": False,
        "witness_chain_research_started": False,
        "witness_chain_constructed": False,
        "release_hold_summary_prepared": False,
        "main_physics_target_selection_returned": False,
        "release_assembly_authorized": False,
        "release_assembly_authorized_by_review": False,
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
        "tranche_004_future_route_required": program.get("tranche_004_future_route_required"),
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
        else "REMEDIATE_V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_RESULT_REVIEW",
        "selected_next_target_kind": "bounded_source_map_witness_chain_research_packet_preparation_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_ONLY_"
            "NO_RESEARCH_EXECUTION_SOURCE_MAP_CLOSURE_RELEASE_ASSEMBLY_OR_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained-tranche-004 future remediation program result review accepts "
            "the remediation program as planning only and selects one next bounded route: "
            "preparation of a source-map witness-chain research packet. It does not "
            "prepare that packet, execute research, construct a witness chain, downgrade "
            "tranche 004, assemble release, mark readiness, discharge theorem/proof debt "
            "or retained assumptions, claim source-map or QFT-GR seam closure, authorize "
            "Phase 2, validate empirically, promote the master action, or make an "
            "external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_result_review(
    *,
    program_path: Path = DEFAULT_PROGRAM_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(
        program_path=program_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha retained tranche 004 future remediation program "
            "result review."
        )
    )
    parser.add_argument("--program", type=Path, default=DEFAULT_PROGRAM_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    program_path = ns.program if ns.program.is_absolute() else (REPO_ROOT / ns.program)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        program_path=program_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_future_remediation_program_result_review_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
