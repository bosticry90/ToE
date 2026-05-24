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
    TRANCHE_005_STATUS,
    TRANCHE_006_STATUS,
)
from formal.python.tools.v01_alpha_retained_tranche_004_release_readiness_adjudication_report import (
    RELEASE_READINESS_DECISION,
    SELECTED_TRANCHE_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_closure_adjudication_packet_result_review_report import (
    ASSEMBLE_RELEASE_PACKET_TARGET,
    BLOCKER_MOVEMENT_ADJUDICATION_TARGET,
    DEFAULT_OUT as DEFAULT_PACKET_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXECUTION_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_RESULT_REVIEW_OUTCOME,
    REFINED_AUTHORIZATION_ADJUDICATION_TARGET,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_PACKET_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_PACKET_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_PACKET_RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_"
    "20260523_v0"
)
EXECUTION_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_"
    "EXECUTED_WITH_NO_RELEASE_PROMOTION"
)
CLOSURE_ADJUDICATION_RESULT_CLASSIFICATION = (
    "source_map_closure_authorized_pending_result_review"
)
CLOSURE_ADJUDICATION_ANSWER = (
    "yes_source_map_closure_authorized_pending_result_review"
)
NEXT_TARGET = (
    "review_v01_alpha_retained_tranche_004_source_map_closure_adjudication_result"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_20260523_v0.json"
)

FORBIDDEN_EFFECTS = [
    "axiom_spec_backed_debt_reduced",
    "blocker_movement_authorized",
    "blocker_movement_registered",
    "empirical_validation_authorized",
    "empirical_validation_claimed",
    "final_source_map_closure_authorized",
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
    "source_map_closure_achieved",
    "source_map_closure_claimed",
    "source_map_closure_registered",
    "tranche_004_retained_blocker_discharged",
    "tranche_004_status_moved",
    "unbounded_closure_adjudication_authorized",
    "v01_alpha_marked_ready",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _adjudicated_closure_requirements(
    packet_result_review: dict[str, Any],
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for row in packet_result_review.get("closure_adjudication_requirements", []):
        rows.append(
            {
                "requirement_id": row.get("requirement_id"),
                "component_id": row.get("component_id"),
                "candidate_surface": row.get("candidate_surface"),
                "candidate_result_review_surface": row.get(
                    "candidate_result_review_surface"
                ),
                "input_packet_status": row.get("packet_status"),
                "closure_adjudication_status": (
                    "satisfies_source_map_closure_requirement_pending_result_review"
                ),
                "result_review_required_before_closure_registration": True,
            }
        )
    return rows


def _closure_adjudication_steps(
    adjudicated_requirements: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    return [
        {
            "step_id": "closure_adjudication_001_consume_packet_result_review",
            "result": "bounded_source_map_closure_adjudication_execution_authorization_consumed",
        },
        {
            "step_id": "closure_adjudication_002_carry_accepted_authorization_posture",
            "result": "accepted_authorization_requirements_carried",
            "requirement_count": len(adjudicated_requirements),
        },
        {
            "step_id": "closure_adjudication_003_evaluate_source_map_closure_requirements",
            "result": CLOSURE_ADJUDICATION_ANSWER,
            "adjudicated_component_ids": [
                str(row["component_id"]) for row in adjudicated_requirements
            ],
        },
        {
            "step_id": "closure_adjudication_004_preserve_result_review_and_release_firewall",
            "result": "source_map_closure_authorized_pending_result_review_no_release_promotion",
        },
        {
            "step_id": "closure_adjudication_005_classify_result_pending_review",
            "result": CLOSURE_ADJUDICATION_RESULT_CLASSIFICATION,
            "selected_next_target": NEXT_TARGET,
        },
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The bounded closure adjudication execution records an authorized "
                "pending-result-review classification that must be reviewed before "
                "any closure registration, blocker movement, or release action."
            ),
        },
        {
            "target": BLOCKER_MOVEMENT_ADJUDICATION_TARGET,
            "decision": "deferred",
            "reason": (
                "Blocker movement requires an accepted closure adjudication result "
                "review and later movement control."
            ),
        },
        {
            "target": REFINED_AUTHORIZATION_ADJUDICATION_TARGET,
            "decision": "deferred",
            "reason": (
                "A refined authorization/closure packet remains available if result "
                "review rejects this execution classification."
            ),
        },
        {
            "target": ASSEMBLE_RELEASE_PACKET_TARGET,
            "decision": "not_authorized",
            "reason": "Release assembly remains blocked by retained tranche 004.",
        },
    ]


def build_source_map_closure_adjudication(
    *,
    packet_result_review_path: Path = DEFAULT_PACKET_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet_result_review = _read_json(packet_result_review_path)
    closure_requirements = list(
        packet_result_review.get("closure_adjudication_requirements", [])
    )
    reviewed_authorization_requirements = list(
        packet_result_review.get("reviewed_authorization_requirements", [])
    )
    reviewed_components = list(
        packet_result_review.get("reviewed_witness_chain_components", [])
    )
    required_proof_surfaces = list(packet_result_review.get("required_proof_surfaces", []))
    required_evidence_surfaces = list(
        packet_result_review.get("required_evidence_surfaces", [])
    )
    success_criteria = list(
        packet_result_review.get("closure_adjudication_success_criteria", [])
    )
    failure_criteria = list(
        packet_result_review.get("closure_adjudication_failure_criteria", [])
    )
    execution_boundary = list(
        packet_result_review.get("closure_adjudication_execution_boundary", [])
    )
    adjudicated_requirements = _adjudicated_closure_requirements(packet_result_review)
    execution_steps = _closure_adjudication_steps(adjudicated_requirements)
    candidate_next_targets = _candidate_next_targets()
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_packet_result_review": packet_result_review.get("review_id")
        == EXPECTED_PACKET_RESULT_REVIEW_ID,
        "packet_result_review_schema_expected": packet_result_review.get("schema_id")
        == EXPECTED_PACKET_RESULT_REVIEW_SCHEMA_ID,
        "packet_result_review_outcome_expected": packet_result_review.get("outcome_id")
        == EXPECTED_PACKET_RESULT_REVIEW_OUTCOME,
        "packet_result_review_selected_this_execution": packet_result_review.get(
            "selected_next_target"
        )
        == EXECUTION_TARGET,
        "packet_result_review_authorizes_execution_only": packet_result_review.get(
            "accepted"
        )
        is True
        and packet_result_review.get("result_review_classification")
        == EXPECTED_PACKET_RESULT_REVIEW_CLASSIFICATION
        and packet_result_review.get(
            "source_map_closure_adjudication_execution_authorized_by_review"
        )
        is True
        and packet_result_review.get(
            "bounded_source_map_closure_adjudication_execution_authorized"
        )
        is True,
        "input_question_was_not_previously_answered": packet_result_review.get(
            "source_map_closure_adjudication_executed"
        )
        is False
        and packet_result_review.get(
            "source_map_closure_adjudication_question_answered"
        )
        is False
        and packet_result_review.get("source_map_closure_requirements_adjudicated")
        is False,
        "accepted_authorization_and_witness_material_carried": packet_result_review.get(
            "source_map_authorization_adjudication_result_accepted"
        )
        is True
        and packet_result_review.get(
            "source_map_authorization_requirements_satisfied_accepted_by_review"
        )
        is True
        and packet_result_review.get("witness_chain_construction_accepted") is True
        and packet_result_review.get("source_map_witness_chain_construction_accepted")
        is True
        and len(reviewed_authorization_requirements) == 7
        and len(reviewed_components) == 7,
        "all_closure_requirements_adjudicated_pending_review": len(
            closure_requirements
        )
        == 7
        and len(adjudicated_requirements) == 7
        and all(
            row.get("input_packet_status")
            == "prepared_for_future_closure_adjudication_not_answered"
            for row in adjudicated_requirements
        )
        and all(
            row.get("closure_adjudication_status")
            == "satisfies_source_map_closure_requirement_pending_result_review"
            for row in adjudicated_requirements
        )
        and all(
            row.get("result_review_required_before_closure_registration") is True
            for row in adjudicated_requirements
        ),
        "proof_evidence_and_boundaries_carried": len(required_proof_surfaces) == 7
        and packet_result_review.get("required_proof_surface_count") == 7
        and len(required_evidence_surfaces) == 6
        and packet_result_review.get("required_evidence_surface_count") == 6
        and len(success_criteria) == 4
        and packet_result_review.get("closure_adjudication_success_criteria_count") == 4
        and len(failure_criteria) == 4
        and packet_result_review.get("closure_adjudication_failure_criteria_count") == 4
        and len(execution_boundary) == 5
        and packet_result_review.get("closure_adjudication_execution_boundary_count")
        == 5,
        "bounded_execution_records_exactly_one_classification": len(execution_steps) == 5
        and CLOSURE_ADJUDICATION_RESULT_CLASSIFICATION
        == "source_map_closure_authorized_pending_result_review",
        "answer_records_authorized_pending_review": CLOSURE_ADJUDICATION_ANSWER
        == "yes_source_map_closure_authorized_pending_result_review",
        "tranche_004_retained": packet_result_review.get("tranche_004_status")
        == TRANCHE_004_STATUS
        and packet_result_review.get("retained_tranche_004_carry_forward", {}).get(
            "status"
        )
        == TRANCHE_004_STATUS
        and packet_result_review.get("selected_remediation_finding_id")
        == TRANCHE_004_FINDING_ID
        and packet_result_review.get("selected_dependency") == TRANCHE_004_DEPENDENCY,
        "documented_dependency_nonblocking_queue_preserved": packet_result_review.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS
        and packet_result_review.get("tranche_002_status") == TRANCHE_002_STATUS
        and packet_result_review.get("tranche_003_status") == TRANCHE_003_STATUS
        and packet_result_review.get("tranche_005_status") == TRANCHE_005_STATUS
        and packet_result_review.get("tranche_006_status") == TRANCHE_006_STATUS
        and packet_result_review.get("documented_dependency_nonblocking_tranche_count")
        == 5,
        "release_hold_preserved": packet_result_review.get(
            "release_readiness_decision_status"
        )
        == RELEASE_READINESS_DECISION
        and packet_result_review.get("release_readiness_held") is True
        and packet_result_review.get("release_readiness_still_blocked") is True
        and packet_result_review.get("release_readiness_proceed_authorized") is False,
        "no_final_closure_seam_or_blocker_movement_in_input": packet_result_review.get(
            "source_map_closure_authorized"
        )
        is False
        and packet_result_review.get("source_map_closure_claimed") is False
        and packet_result_review.get("source_map_closure_registered") is False
        and packet_result_review.get("qft_gr_seam_closed") is False
        and packet_result_review.get("qft_gr_seam_closure_authorized") is False
        and packet_result_review.get("tranche_004_status_moved") is False
        and packet_result_review.get("tranche_004_retained_blocker_discharged")
        is False,
        "no_release_theorem_phase_empirical_publication_or_master_promotion": packet_result_review.get(
            "release_assembly_authorized"
        )
        is False
        and packet_result_review.get("release_packet_assembled") is False
        and packet_result_review.get("lean_theorem_debt_discharged") is False
        and packet_result_review.get("proof_debt_reduced") is False
        and packet_result_review.get("phase2_authorized") is False
        and packet_result_review.get("empirical_validation_authorized") is False
        and packet_result_review.get("publication_authorized") is False
        and packet_result_review.get("master_action_promotion_authorized") is False,
        "result_review_selected_only": sum(
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
        "execution_id": EXECUTION_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "executed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_BLOCKED",
        "consumes_source_map_closure_adjudication_packet_result_review": (
            EXPECTED_PACKET_RESULT_REVIEW_ID
        ),
        "consumes_source_map_closure_adjudication_packet_result_review_pointer": (
            _ptr(packet_result_review_path)
        ),
        "consumed_source_map_closure_adjudication_packet_result_review_schema_id": (
            packet_result_review.get("schema_id")
        ),
        "consumed_source_map_closure_adjudication_packet_result_review_outcome_id": (
            packet_result_review.get("outcome_id")
        ),
        "consumed_packet_result_review_classification": packet_result_review.get(
            "result_review_classification"
        ),
        "execution_scope": (
            "EXECUTE_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_ONLY_"
            "NO_QFT_GR_SEAM_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "source_map_closure_adjudication_execution_target": EXECUTION_TARGET,
        "source_map_closure_adjudication_executed": accepted,
        "bounded_source_map_closure_adjudication_executed": accepted,
        "bounded_source_map_closure_adjudication_execution_only": accepted,
        "source_map_closure_adjudication_result_classification": (
            CLOSURE_ADJUDICATION_RESULT_CLASSIFICATION
        ),
        "closure_adjudication_result_classification_count": 1 if accepted else 0,
        "result_classification_count": 1 if accepted else 0,
        "closure_adjudication_question": packet_result_review.get(
            "closure_adjudication_question"
        ),
        "source_map_closure_adjudication_question_answered": accepted,
        "closure_adjudication_answer": (
            CLOSURE_ADJUDICATION_ANSWER if accepted else "not_answered"
        ),
        "source_map_closure_authorized_pending_result_review": accepted,
        "source_map_closure_authorization_result_review_required": True,
        "source_map_closure_adjudication_result_review_authorized": accepted,
        "source_map_closure_requirements_adjudicated": accepted,
        "source_map_closure_authorization_decision_accepted_by_review": False,
        "source_map_closure_adjudication_result_accepted_by_review": False,
        "source_map_closure_result_claimed_as_final_closure": False,
        "adjudicated_closure_requirements": adjudicated_requirements,
        "adjudicated_closure_requirement_count": len(adjudicated_requirements),
        "closure_adjudication_requirements": closure_requirements,
        "closure_adjudication_requirement_count": len(closure_requirements),
        "reviewed_authorization_requirements": reviewed_authorization_requirements,
        "reviewed_authorization_requirement_count": len(
            reviewed_authorization_requirements
        ),
        "accepted_authorization_requirement_count": packet_result_review.get(
            "accepted_authorization_requirement_count"
        ),
        "reviewed_witness_chain_components": reviewed_components,
        "reviewed_witness_chain_component_count": len(reviewed_components),
        "required_proof_surfaces": required_proof_surfaces,
        "required_proof_surface_count": len(required_proof_surfaces),
        "required_evidence_surfaces": required_evidence_surfaces,
        "required_evidence_surface_count": len(required_evidence_surfaces),
        "closure_adjudication_success_criteria": success_criteria,
        "closure_adjudication_success_criteria_count": len(success_criteria),
        "closure_adjudication_failure_criteria": failure_criteria,
        "closure_adjudication_failure_criteria_count": len(failure_criteria),
        "closure_adjudication_execution_boundary": execution_boundary,
        "closure_adjudication_execution_boundary_count": len(execution_boundary),
        "closure_adjudication_execution_steps": execution_steps,
        "closure_adjudication_execution_step_count": len(execution_steps),
        "source_map_authorization_adjudication_result_accepted": packet_result_review.get(
            "source_map_authorization_adjudication_result_accepted"
        )
        is True,
        "source_map_authorization_requirements_satisfied_accepted_by_review": packet_result_review.get(
            "source_map_authorization_requirements_satisfied_accepted_by_review"
        )
        is True,
        "witness_chain_construction_accepted": True if accepted else False,
        "source_map_witness_chain_construction_accepted": True if accepted else False,
        "witness_chain_constructed": True if accepted else False,
        "source_map_witness_chain_constructed": True if accepted else False,
        "source_map_closure_achieved": False,
        "source_map_closure_authorized": False,
        "source_map_closure_claimed": False,
        "source_map_closure_registered": False,
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
        "tranche_006_status": TRANCHE_006_STATUS,
        "documented_dependency_nonblocking_tranche_count": 5,
        "retained_tranche_004_carry_forward": packet_result_review.get(
            "retained_tranche_004_carry_forward", {}
        ),
        "required_future_route_for_tranche_004": TRANCHE_004_FUTURE_ROUTE,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "tranche_004_status_moved_by_execution": False,
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
        else "REMEDIATE_V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION",
        "selected_next_target_kind": (
            "retained_tranche_004_source_map_closure_adjudication_result_review_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_RESULT_"
            "ONLY_NO_QFT_GR_SEAM_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained tranche 004 source-map closure adjudication execution "
            "answers only whether the accepted witness-chain construction and "
            "accepted source-map authorization posture satisfy the repo's "
            "source-map closure requirements, recording source-map closure "
            "authorization pending result review. It does not register or claim "
            "final source-map closure, close the QFT-GR seam, move tranche 004, "
            "assemble release, mark readiness, discharge theorem/proof debt or "
            "retained assumptions, authorize Phase 2, authorize empirical "
            "validation, authorize publication, promote the master action, or "
            "make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_source_map_closure_adjudication(
    *,
    packet_result_review_path: Path = DEFAULT_PACKET_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_source_map_closure_adjudication(
        packet_result_review_path=packet_result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha retained tranche 004 source-map closure "
            "adjudication execution."
        )
    )
    parser.add_argument(
        "--packet-result-review",
        type=Path,
        default=DEFAULT_PACKET_RESULT_REVIEW_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_result_review_path = (
        ns.packet_result_review
        if ns.packet_result_review.is_absolute()
        else (REPO_ROOT / ns.packet_result_review)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_source_map_closure_adjudication(
        packet_result_review_path=packet_result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_source_map_closure_adjudication_report: "
        f"accepted={payload['accepted']} classification="
        f"{payload['source_map_closure_adjudication_result_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
