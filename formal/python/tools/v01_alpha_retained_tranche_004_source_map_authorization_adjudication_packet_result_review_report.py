from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    DEFAULT_CAPTURED_AT_UTC,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_004_DEPENDENCY,
    TRANCHE_004_FINDING_ID,
    TRANCHE_004_FUTURE_ROUTE,
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
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_authorization_adjudication_packet_report import (
    ADJUDICATION_EXECUTION_TARGET,
    ADJUDICATION_RESULT_REVIEW_TARGET,
    ASSEMBLE_RELEASE_PACKET_TARGET,
    DEFAULT_OUT as DEFAULT_ADJUDICATION_PACKET_PATH,
    OUTCOME_ID as EXPECTED_ADJUDICATION_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_ADJUDICATION_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_ADJUDICATION_PACKET_ID,
    REFINED_CONSTRUCTION_TARGET,
    SCHEMA_ID as EXPECTED_ADJUDICATION_PACKET_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_"
    "PACKET_RESULT_REVIEW_20260523_v0"
)
REVIEW_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_"
    "PACKET_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_"
    "PACKET_RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_BOUNDED_ADJUDICATION_"
    "EXECUTION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "source_map_authorization_adjudication_packet_accepted_bounded_adjudication_"
    "execution_authorized_only"
)
CONSUMED_TARGET = (
    "review_v01_alpha_retained_tranche_004_source_map_authorization_adjudication_"
    "packet_result"
)
NEXT_TARGET = ADJUDICATION_EXECUTION_TARGET

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_"
        "PACKET_RESULT_REVIEW_20260523_v0.json"
    )
)

FORBIDDEN_EFFECTS = [
    "adjudication_answer_recorded",
    "adjudication_packet_claimed_as_closure",
    "axiom_spec_backed_debt_reduced",
    "blocker_movement_authorized",
    "blocker_movement_registered",
    "empirical_validation_authorized",
    "empirical_validation_claimed",
    "lean_theorem_debt_discharged",
    "master_action_promotion_authorized",
    "phase2_authorized",
    "proof_debt_reduced",
    "publication_authorized",
    "qft_gr_seam_closed",
    "qft_gr_seam_closure_authorized",
    "qft_gr_seam_closure_claimed",
    "qft_gr_source_map_semantic_closure_claimed",
    "readiness_marking_authorized",
    "release_assembly_authorized",
    "release_packet_assembled",
    "retained_assumptions_discharged",
    "source_map_authorization_adjudication_executed",
    "source_map_closure_achieved",
    "source_map_closure_authorized",
    "source_map_closure_claimed",
    "source_map_closure_requirements_adjudicated",
    "tranche_004_retained_blocker_discharged",
    "tranche_004_status_moved",
    "unbounded_adjudication_authorized",
    "v01_alpha_marked_ready",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The adjudication packet is accepted for bounded execution only; "
                "execution must record a conservative result classification and "
                "still cannot promote release or claim closure by this review."
            ),
        },
        {
            "target": ADJUDICATION_RESULT_REVIEW_TARGET,
            "decision": "deferred",
            "reason": "Adjudication result review is available only after bounded adjudication execution.",
        },
        {
            "target": REFINED_CONSTRUCTION_TARGET,
            "decision": "deferred",
            "reason": "Refined construction remains available if adjudication execution cannot proceed.",
        },
        {
            "target": ASSEMBLE_RELEASE_PACKET_TARGET,
            "decision": "not_authorized",
            "reason": "Release assembly remains blocked by retained tranche 004.",
        },
    ]


def build_source_map_authorization_adjudication_packet_result_review(
    *,
    adjudication_packet_path: Path = DEFAULT_ADJUDICATION_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(adjudication_packet_path)
    adjudication_requirements = list(packet.get("adjudication_requirements", []))
    reviewed_components = list(packet.get("reviewed_witness_chain_components", []))
    required_proof_surfaces = list(packet.get("required_proof_surfaces", []))
    required_evidence_surfaces = list(packet.get("required_evidence_surfaces", []))
    success_criteria = list(packet.get("adjudication_success_criteria", []))
    failure_criteria = list(packet.get("adjudication_failure_criteria", []))
    execution_boundary = list(packet.get("adjudication_execution_boundary", []))
    candidate_next_targets = _candidate_next_targets()
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_adjudication_packet": packet.get("packet_id")
        == EXPECTED_ADJUDICATION_PACKET_ID,
        "adjudication_packet_schema_expected": packet.get("schema_id")
        == EXPECTED_ADJUDICATION_PACKET_SCHEMA_ID,
        "adjudication_packet_outcome_expected": packet.get("outcome_id")
        == EXPECTED_ADJUDICATION_PACKET_OUTCOME,
        "adjudication_packet_selected_this_review": packet.get("selected_next_target")
        == CONSUMED_TARGET,
        "packet_prepared_question_only": packet.get("accepted") is True
        and packet.get("prepared") is True
        and packet.get("source_map_authorization_adjudication_packet_prepared") is True
        and packet.get("source_map_authorization_adjudication_packet_preparation_only")
        is True
        and packet.get("packet_classification")
        == EXPECTED_ADJUDICATION_PACKET_CLASSIFICATION,
        "packet_did_not_execute_or_answer": packet.get(
            "source_map_authorization_adjudication_execution_authorized_by_packet"
        )
        is False
        and packet.get("source_map_authorization_adjudication_execution_authorized")
        is False
        and packet.get("source_map_authorization_adjudication_executed") is False
        and packet.get("adjudication_question_answered") is False
        and packet.get("source_map_closure_requirements_adjudicated") is False,
        "accepted_witness_chain_material_carried": packet.get(
            "witness_chain_construction_accepted"
        )
        is True
        and packet.get("source_map_witness_chain_construction_accepted") is True
        and packet.get("witness_chain_constructed") is True
        and packet.get("source_map_witness_chain_constructed") is True
        and len(reviewed_components) == 7
        and packet.get("accepted_witness_chain_component_count") == 7,
        "adjudication_requirements_reviewable": len(adjudication_requirements) == 7
        and packet.get("adjudication_requirement_count") == 7
        and all(
            row.get("packet_status")
            == "prepared_for_future_adjudication_not_adjudicated"
            for row in adjudication_requirements
        ),
        "proof_evidence_and_boundaries_carried": len(required_proof_surfaces) == 7
        and packet.get("required_proof_surface_count") == 7
        and len(required_evidence_surfaces) == 6
        and packet.get("required_evidence_surface_count") == 6
        and len(success_criteria) == 4
        and packet.get("adjudication_success_criteria_count") == 4
        and len(failure_criteria) == 4
        and packet.get("adjudication_failure_criteria_count") == 4
        and len(execution_boundary) == 5
        and packet.get("adjudication_execution_boundary_count") == 5,
        "tranche_004_retained": packet.get("tranche_004_status") == TRANCHE_004_STATUS
        and packet.get("retained_tranche_004_carry_forward", {}).get("status")
        == TRANCHE_004_STATUS
        and packet.get("selected_remediation_finding_id") == TRANCHE_004_FINDING_ID
        and packet.get("selected_dependency") == TRANCHE_004_DEPENDENCY,
        "documented_dependency_nonblocking_queue_preserved": packet.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS
        and packet.get("tranche_002_status") == TRANCHE_002_STATUS
        and packet.get("tranche_003_status") == TRANCHE_003_STATUS
        and packet.get("tranche_005_status") == TRANCHE_005_STATUS
        and packet.get("tranche_005_dependency") == TRANCHE_005_DEPENDENCY
        and packet.get("tranche_006_status") == TRANCHE_006_STATUS
        and packet.get("tranche_006_dependency") == TRANCHE_006_DEPENDENCY
        and packet.get("tranche_006_dependency_class") == TRANCHE_006_DEPENDENCY_CLASS
        and packet.get("tranche_006_dependency_finding_id") == TRANCHE_006_FINDING_ID
        and packet.get("documented_dependency_nonblocking_tranche_count") == 5,
        "release_hold_preserved": packet.get("release_readiness_decision_status")
        == RELEASE_READINESS_DECISION
        and packet.get("release_readiness_held") is True
        and packet.get("release_readiness_still_blocked") is True
        and packet.get("release_readiness_proceed_authorized") is False,
        "no_closure_seam_or_blocker_movement_in_input": packet.get(
            "source_map_closure_claimed"
        )
        is False
        and packet.get("source_map_closure_authorized") is False
        and packet.get("qft_gr_seam_closed") is False
        and packet.get("qft_gr_seam_closure_authorized") is False
        and packet.get("tranche_004_status_moved") is False
        and packet.get("tranche_004_retained_blocker_discharged") is False,
        "no_release_theorem_phase_empirical_publication_or_master_promotion": packet.get(
            "release_assembly_authorized"
        )
        is False
        and packet.get("release_packet_assembled") is False
        and packet.get("lean_theorem_debt_discharged") is False
        and packet.get("proof_debt_reduced") is False
        and packet.get("phase2_authorized") is False
        and packet.get("empirical_validation_authorized") is False
        and packet.get("publication_authorized") is False
        and packet.get("master_action_promotion_authorized") is False,
        "bounded_adjudication_execution_selected_only": sum(
            1 for row in candidate_next_targets if row["decision"] == "selected"
        )
        == 1
        and candidate_next_targets[0]["target"] == NEXT_TARGET,
        "forbidden_effects_all_false": all(
            value is False for value in forbidden_effect_status.values()
        ),
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
        else (
            "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_"
            "PACKET_RESULT_REVIEW_BLOCKED"
        ),
        "consumes_source_map_authorization_adjudication_packet": (
            EXPECTED_ADJUDICATION_PACKET_ID
        ),
        "consumes_source_map_authorization_adjudication_packet_pointer": _ptr(
            adjudication_packet_path
        ),
        "consumed_source_map_authorization_adjudication_packet_schema_id": packet.get(
            "schema_id"
        ),
        "consumed_source_map_authorization_adjudication_packet_outcome_id": packet.get(
            "outcome_id"
        ),
        "consumed_packet_classification": packet.get("packet_classification"),
        "review_scope": (
            "REVIEW_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_"
            "PACKET_RESULT_ONLY_NO_ADJUDICATION_EXECUTION_SOURCE_MAP_CLOSURE_"
            "BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "source_map_authorization_adjudication_packet_result_reviewed": accepted,
        "source_map_authorization_adjudication_packet_result_accepted": accepted,
        "source_map_authorization_adjudication_packet_accepted_for_bounded_execution_only": accepted,
        "source_map_authorization_adjudication_packet_accepted_as_closure_evidence": False,
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "result_classification_count": 1 if accepted else 0,
        "source_map_authorization_adjudication_packet_prepared": packet.get(
            "source_map_authorization_adjudication_packet_prepared"
        )
        is True,
        "source_map_authorization_adjudication_packet_preparation_only": packet.get(
            "source_map_authorization_adjudication_packet_preparation_only"
        )
        is True,
        "source_map_authorization_adjudication_execution_authorized_by_packet": False,
        "bounded_source_map_authorization_adjudication_execution_authorized": accepted,
        "source_map_authorization_adjudication_execution_authorized_by_review": accepted,
        "source_map_authorization_adjudication_execution_authorized": accepted,
        "source_map_authorization_adjudication_executed": False,
        "source_map_authorization_adjudication_execution_target": NEXT_TARGET,
        "post_adjudication_result_review_target": ADJUDICATION_RESULT_REVIEW_TARGET,
        "adjudication_question": packet.get("adjudication_question"),
        "adjudication_question_answered": False,
        "source_map_closure_requirements_adjudicated": False,
        "source_map_closure_authorization_decision_made": False,
        "adjudication_requirements": adjudication_requirements,
        "adjudication_requirement_count": len(adjudication_requirements),
        "reviewed_witness_chain_components": reviewed_components,
        "reviewed_witness_chain_component_count": len(reviewed_components),
        "accepted_witness_chain_component_count": packet.get(
            "accepted_witness_chain_component_count"
        ),
        "required_proof_surfaces": required_proof_surfaces,
        "required_proof_surface_count": len(required_proof_surfaces),
        "required_evidence_surfaces": required_evidence_surfaces,
        "required_evidence_surface_count": len(required_evidence_surfaces),
        "adjudication_success_criteria": success_criteria,
        "adjudication_success_criteria_count": len(success_criteria),
        "adjudication_failure_criteria": failure_criteria,
        "adjudication_failure_criteria_count": len(failure_criteria),
        "adjudication_execution_boundary": execution_boundary,
        "adjudication_execution_boundary_count": len(execution_boundary),
        "witness_chain_construction_accepted": True if accepted else False,
        "source_map_witness_chain_construction_accepted": True if accepted else False,
        "witness_chain_constructed": True if accepted else False,
        "source_map_witness_chain_constructed": True if accepted else False,
        "witness_chain_constructed_claimed": True if accepted else False,
        "source_map_witness_chain_constructed_claimed": True if accepted else False,
        "source_map_closure_achieved": False,
        "source_map_closure_authorized": False,
        "source_map_closure_claimed": False,
        "qft_gr_source_map_semantic_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "qft_gr_seam_closure_authorized": False,
        "qft_gr_seam_closure_claimed": False,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": TRANCHE_004_FINDING_ID,
        "selected_dependency": TRANCHE_004_DEPENDENCY,
        "selected_dependency_class": "blocked_bridge_authorization_dependency",
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
        "documented_dependency_nonblocking_tranche_count": 5,
        "retained_tranche_004_carry_forward": packet.get(
            "retained_tranche_004_carry_forward", {}
        ),
        "required_future_route_for_tranche_004": TRANCHE_004_FUTURE_ROUTE,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "tranche_004_status_moved_by_review": False,
        "tranche_004_status_moved": False,
        "tranche_004_retained_blocker_discharged": False,
        "blocker_movement_authorized": False,
        "blocker_movement_registered": False,
        "release_readiness_decision_status": RELEASE_READINESS_DECISION,
        "release_readiness_held": True,
        "release_readiness_still_blocked": True,
        "release_readiness_proceed_authorized": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "readiness_marking_authorized": False,
        "v01_alpha_marked_ready": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "phase2_authorized": False,
        "empirical_validation_authorized": False,
        "empirical_validation_claimed": False,
        "publication_authorized": False,
        "master_action_promotion_authorized": False,
        "forbidden_effect_status": forbidden_effect_status,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_"
            "ADJUDICATION_PACKET_RESULT_REVIEW"
        ),
        "selected_next_target_kind": (
            "bounded_source_map_authorization_adjudication_execution_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "EXECUTE_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_"
            "ONLY_NO_SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained tranche 004 source-map authorization adjudication packet "
            "result review accepts the prepared packet and authorizes only bounded "
            "source-map authorization adjudication execution as the next target. It "
            "does not execute adjudication, answer the source-map semantic-closure "
            "authorization question, claim source-map closure, close the QFT-GR seam, "
            "move tranche 004, assemble release, mark readiness, discharge theorem/"
            "proof debt or retained assumptions, authorize Phase 2, authorize empirical "
            "validation, authorize publication, promote the master action, or make an "
            "external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_source_map_authorization_adjudication_packet_result_review(
    *,
    adjudication_packet_path: Path = DEFAULT_ADJUDICATION_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_source_map_authorization_adjudication_packet_result_review(
        adjudication_packet_path=adjudication_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha retained tranche 004 source-map authorization "
            "adjudication packet result review."
        )
    )
    parser.add_argument(
        "--adjudication-packet",
        type=Path,
        default=DEFAULT_ADJUDICATION_PACKET_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    adjudication_packet_path = (
        ns.adjudication_packet
        if ns.adjudication_packet.is_absolute()
        else (REPO_ROOT / ns.adjudication_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_source_map_authorization_adjudication_packet_result_review(
        adjudication_packet_path=adjudication_packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_source_map_authorization_adjudication_packet_result_review_report: "
        f"accepted={payload['accepted']} classification={payload['result_review_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
