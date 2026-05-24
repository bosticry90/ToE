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
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_authorization_adjudication_report import (
    ADJUDICATION_ANSWER,
    ADJUDICATION_RESULT_CLASSIFICATION as EXPECTED_ADJUDICATION_RESULT_CLASSIFICATION,
    ASSEMBLE_RELEASE_PACKET_TARGET,
    DEFAULT_OUT as DEFAULT_ADJUDICATION_EXECUTION_PATH,
    EXECUTION_ID as EXPECTED_ADJUDICATION_EXECUTION_ID,
    OUTCOME_ID as EXPECTED_ADJUDICATION_EXECUTION_OUTCOME,
    REFINED_ADJUDICATION_PACKET_TARGET,
    SCHEMA_ID as EXPECTED_ADJUDICATION_EXECUTION_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_"
    "RESULT_REVIEW_20260523_v0"
)
REVIEW_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_"
    "RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_"
    "RESULT_REVIEW_ACCEPTS_REQUIREMENTS_SATISFIED_AND_AUTHORIZES_SOURCE_MAP_"
    "CLOSURE_ADJUDICATION_PREPARATION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "source_map_authorization_requirements_satisfied_accepted_source_map_closure_"
    "adjudication_packet_preparation_only"
)
CONSUMED_TARGET = (
    "review_v01_alpha_retained_tranche_004_source_map_authorization_"
    "adjudication_result"
)
NEXT_TARGET = (
    "prepare_v01_alpha_retained_tranche_004_source_map_closure_adjudication_packet"
)
SOURCE_MAP_CLOSURE_ADJUDICATION_EXECUTION_TARGET = (
    "execute_v01_alpha_retained_tranche_004_source_map_closure_adjudication"
)
BLOCKER_MOVEMENT_ADJUDICATION_TARGET = (
    "prepare_v01_alpha_retained_tranche_004_blocker_movement_adjudication_packet"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_"
        "RESULT_REVIEW_20260523_v0.json"
    )
)

FORBIDDEN_EFFECTS = [
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
    "source_map_closure_achieved",
    "source_map_closure_adjudication_executed",
    "source_map_closure_adjudication_packet_prepared",
    "source_map_closure_authorized",
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


def _reviewed_requirements(execution: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for row in execution.get("adjudicated_requirements", []):
        rows.append(
            {
                "requirement_id": row.get("requirement_id"),
                "component_id": row.get("component_id"),
                "candidate_surface": row.get("candidate_surface"),
                "candidate_result_review_surface": row.get(
                    "candidate_result_review_surface"
                ),
                "execution_adjudication_status": row.get("adjudication_status"),
                "result_review_status": (
                    "accepted_requirements_satisfied_for_source_map_closure_"
                    "adjudication_packet_preparation_only"
                ),
                "closure_status": "not_source_map_closure_by_result_review_alone",
                "closure_adjudication_packet_preparation_authorized": True,
            }
        )
    return rows


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The adjudication execution result is accepted as requirements "
                "satisfied only for preparing the separate source-map closure "
                "adjudication packet."
            ),
        },
        {
            "target": SOURCE_MAP_CLOSURE_ADJUDICATION_EXECUTION_TARGET,
            "decision": "deferred",
            "reason": "Closure adjudication execution requires a prepared and reviewed packet first.",
        },
        {
            "target": BLOCKER_MOVEMENT_ADJUDICATION_TARGET,
            "decision": "deferred",
            "reason": (
                "Blocker movement remains unavailable until a later closure "
                "adjudication execution and result review authorize it."
            ),
        },
        {
            "target": REFINED_ADJUDICATION_PACKET_TARGET,
            "decision": "deferred",
            "reason": "Refinement remains available if a later packet review rejects this route.",
        },
        {
            "target": ASSEMBLE_RELEASE_PACKET_TARGET,
            "decision": "not_authorized",
            "reason": "Release assembly remains blocked by retained tranche 004.",
        },
    ]


def build_source_map_authorization_adjudication_result_review(
    *,
    adjudication_execution_path: Path = DEFAULT_ADJUDICATION_EXECUTION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    execution = _read_json(adjudication_execution_path)
    adjudicated_requirements = list(execution.get("adjudicated_requirements", []))
    reviewed_requirements = _reviewed_requirements(execution)
    reviewed_components = list(execution.get("reviewed_witness_chain_components", []))
    required_proof_surfaces = list(execution.get("required_proof_surfaces", []))
    required_evidence_surfaces = list(execution.get("required_evidence_surfaces", []))
    success_criteria = list(execution.get("adjudication_success_criteria", []))
    failure_criteria = list(execution.get("adjudication_failure_criteria", []))
    execution_boundary = list(execution.get("adjudication_execution_boundary", []))
    execution_steps = list(execution.get("adjudication_execution_steps", []))
    candidate_next_targets = _candidate_next_targets()
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_source_map_authorization_adjudication_execution": execution.get(
            "execution_id"
        )
        == EXPECTED_ADJUDICATION_EXECUTION_ID,
        "adjudication_execution_schema_expected": execution.get("schema_id")
        == EXPECTED_ADJUDICATION_EXECUTION_SCHEMA_ID,
        "adjudication_execution_outcome_expected": execution.get("outcome_id")
        == EXPECTED_ADJUDICATION_EXECUTION_OUTCOME,
        "adjudication_execution_selected_this_review": execution.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "classification_is_requirements_satisfied_pending_review": execution.get(
            "source_map_authorization_adjudication_result_classification"
        )
        == EXPECTED_ADJUDICATION_RESULT_CLASSIFICATION
        and execution.get("adjudication_result_classification_count") == 1,
        "execution_answered_narrow_question_pending_review": execution.get(
            "accepted"
        )
        is True
        and execution.get("executed") is True
        and execution.get("source_map_authorization_adjudication_executed") is True
        and execution.get("bounded_source_map_authorization_adjudication_executed")
        is True
        and execution.get("bounded_source_map_authorization_adjudication_execution_only")
        is True
        and execution.get("adjudication_question_answered") is True
        and execution.get("adjudication_answer") == ADJUDICATION_ANSWER
        and execution.get(
            "source_map_authorization_requirements_satisfied_pending_result_review"
        )
        is True
        and execution.get(
            "source_map_semantic_closure_authorization_requirements_satisfied_pending_result_review"
        )
        is True
        and execution.get("source_map_closure_authorization_result_review_required")
        is True,
        "review_accepts_requirements_satisfied_status_explicitly": len(
            reviewed_requirements
        )
        == 7
        and all(
            row.get("execution_adjudication_status")
            == "satisfies_source_map_authorization_requirement_pending_result_review"
            for row in reviewed_requirements
        )
        and all(
            row.get("result_review_status")
            == (
                "accepted_requirements_satisfied_for_source_map_closure_"
                "adjudication_packet_preparation_only"
            )
            for row in reviewed_requirements
        ),
        "all_adjudicated_requirements_reviewed": len(adjudicated_requirements) == 7
        and execution.get("adjudicated_requirement_count") == 7
        and all(
            row.get("result_review_required_before_closure") is True
            for row in adjudicated_requirements
        ),
        "accepted_witness_chain_material_carried": len(reviewed_components) == 7
        and execution.get("reviewed_witness_chain_component_count") == 7
        and execution.get("accepted_witness_chain_component_count") == 7
        and execution.get("witness_chain_construction_accepted") is True
        and execution.get("source_map_witness_chain_construction_accepted") is True
        and execution.get("witness_chain_constructed") is True
        and execution.get("source_map_witness_chain_constructed") is True,
        "proof_evidence_and_boundaries_carried": len(required_proof_surfaces) == 7
        and execution.get("required_proof_surface_count") == 7
        and len(required_evidence_surfaces) == 6
        and execution.get("required_evidence_surface_count") == 6
        and len(success_criteria) == 4
        and execution.get("adjudication_success_criteria_count") == 4
        and len(failure_criteria) == 4
        and execution.get("adjudication_failure_criteria_count") == 4
        and len(execution_boundary) == 5
        and execution.get("adjudication_execution_boundary_count") == 5
        and len(execution_steps) == 5
        and execution.get("adjudication_execution_step_count") == 5,
        "tranche_004_retained": execution.get("tranche_004_status")
        == TRANCHE_004_STATUS
        and execution.get("retained_tranche_004_carry_forward", {}).get("status")
        == TRANCHE_004_STATUS
        and execution.get("selected_remediation_finding_id") == TRANCHE_004_FINDING_ID
        and execution.get("selected_dependency") == TRANCHE_004_DEPENDENCY,
        "documented_dependency_nonblocking_queue_preserved": execution.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS
        and execution.get("tranche_002_status") == TRANCHE_002_STATUS
        and execution.get("tranche_003_status") == TRANCHE_003_STATUS
        and execution.get("tranche_005_status") == TRANCHE_005_STATUS
        and execution.get("tranche_005_dependency") == TRANCHE_005_DEPENDENCY
        and execution.get("tranche_006_status") == TRANCHE_006_STATUS
        and execution.get("tranche_006_dependency") == TRANCHE_006_DEPENDENCY
        and execution.get("tranche_006_dependency_class") == TRANCHE_006_DEPENDENCY_CLASS
        and execution.get("tranche_006_dependency_finding_id")
        == TRANCHE_006_FINDING_ID
        and execution.get("documented_dependency_nonblocking_tranche_count") == 5,
        "release_hold_preserved": execution.get("release_readiness_decision_status")
        == RELEASE_READINESS_DECISION
        and execution.get("release_readiness_held") is True
        and execution.get("release_readiness_still_blocked") is True
        and execution.get("release_readiness_proceed_authorized") is False,
        "no_closure_seam_or_blocker_movement_in_input": execution.get(
            "source_map_closure_authorized"
        )
        is False
        and execution.get("source_map_closure_claimed") is False
        and execution.get("source_map_closure_registered") is False
        and execution.get("qft_gr_seam_closed") is False
        and execution.get("qft_gr_seam_closure_authorized") is False
        and execution.get("tranche_004_status_moved") is False
        and execution.get("tranche_004_retained_blocker_discharged") is False,
        "no_release_theorem_phase_empirical_publication_or_master_promotion": execution.get(
            "release_assembly_authorized"
        )
        is False
        and execution.get("release_packet_assembled") is False
        and execution.get("lean_theorem_debt_discharged") is False
        and execution.get("proof_debt_reduced") is False
        and execution.get("phase2_authorized") is False
        and execution.get("empirical_validation_authorized") is False
        and execution.get("publication_authorized") is False
        and execution.get("master_action_promotion_authorized") is False,
        "source_map_closure_adjudication_packet_preparation_selected_only": sum(
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
            "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_"
            "ADJUDICATION_RESULT_REVIEW_BLOCKED"
        ),
        "consumes_source_map_authorization_adjudication_execution": (
            EXPECTED_ADJUDICATION_EXECUTION_ID
        ),
        "consumes_source_map_authorization_adjudication_execution_pointer": _ptr(
            adjudication_execution_path
        ),
        "consumed_source_map_authorization_adjudication_schema_id": execution.get(
            "schema_id"
        ),
        "consumed_source_map_authorization_adjudication_outcome_id": execution.get(
            "outcome_id"
        ),
        "consumed_source_map_authorization_adjudication_result_classification": (
            execution.get("source_map_authorization_adjudication_result_classification")
        ),
        "review_scope": (
            "REVIEW_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_"
            "RESULT_ONLY_NO_SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "source_map_authorization_adjudication_result_reviewed": accepted,
        "source_map_authorization_adjudication_result_accepted": accepted,
        "requirements_satisfied_status_accepted_by_review": accepted,
        "source_map_authorization_requirements_satisfied_accepted_by_review": accepted,
        "source_map_authorization_requirements_satisfied_accepted_for_closure_adjudication_packet_preparation_only": accepted,
        "source_map_authorization_result_accepted_as_closure_evidence": False,
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "result_classification_count": 1 if accepted else 0,
        "adjudication_result_classification_count": 1 if accepted else 0,
        "adjudication_question": execution.get("adjudication_question"),
        "adjudication_question_answered": execution.get("adjudication_question_answered")
        is True,
        "adjudication_answer": execution.get("adjudication_answer"),
        "adjudication_answer_accepted_by_review": accepted,
        "source_map_authorization_requirements_satisfied_pending_result_review": (
            execution.get(
                "source_map_authorization_requirements_satisfied_pending_result_review"
            )
            is True
        ),
        "source_map_semantic_closure_authorization_requirements_satisfied_pending_result_review": (
            execution.get(
                "source_map_semantic_closure_authorization_requirements_satisfied_pending_result_review"
            )
            is True
        ),
        "source_map_closure_authorization_requirements_decision_recorded": (
            execution.get(
                "source_map_closure_authorization_requirements_decision_recorded"
            )
            is True
        ),
        "source_map_closure_authorization_decision_accepted_by_review": False,
        "source_map_closure_authorization_result_review_required": False,
        "source_map_closure_adjudication_packet_preparation_authorized": accepted,
        "source_map_closure_adjudication_packet_preparation_only": accepted,
        "source_map_closure_adjudication_packet_prepared": False,
        "source_map_closure_adjudication_execution_authorized": False,
        "source_map_closure_adjudication_executed": False,
        "source_map_closure_adjudication_result_review_authorized": False,
        "reviewed_authorization_requirements": reviewed_requirements,
        "reviewed_authorization_requirement_count": len(reviewed_requirements),
        "accepted_authorization_requirement_count": len(reviewed_requirements)
        if accepted
        else 0,
        "adjudicated_requirements": adjudicated_requirements,
        "adjudicated_requirement_count": len(adjudicated_requirements),
        "reviewed_witness_chain_components": reviewed_components,
        "reviewed_witness_chain_component_count": len(reviewed_components),
        "accepted_witness_chain_component_count": execution.get(
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
        "adjudication_execution_steps": execution_steps,
        "adjudication_execution_step_count": len(execution_steps),
        "witness_chain_construction_accepted": True if accepted else False,
        "source_map_witness_chain_construction_accepted": True if accepted else False,
        "witness_chain_constructed": True if accepted else False,
        "source_map_witness_chain_constructed": True if accepted else False,
        "witness_chain_constructed_claimed": True if accepted else False,
        "source_map_witness_chain_constructed_claimed": True if accepted else False,
        "source_map_closure_requirements_adjudicated": True if accepted else False,
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
        "tranche_005_dependency": TRANCHE_005_DEPENDENCY,
        "tranche_006_status": TRANCHE_006_STATUS,
        "tranche_006_dependency": TRANCHE_006_DEPENDENCY,
        "tranche_006_dependency_class": TRANCHE_006_DEPENDENCY_CLASS,
        "tranche_006_dependency_finding_id": TRANCHE_006_FINDING_ID,
        "documented_dependency_nonblocking_tranche_count": 5,
        "retained_tranche_004_carry_forward": execution.get(
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
            "ADJUDICATION_RESULT_REVIEW"
        ),
        "selected_next_target_kind": (
            "retained_tranche_004_source_map_closure_adjudication_packet_"
            "preparation_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_"
            "PACKET_ONLY_NO_SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "closure_adjudication_question": (
            "Given that source-map authorization requirements were accepted, can "
            "source-map closure be adjudicated under the repo's release-control rules?"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained tranche 004 source-map authorization adjudication result "
            "review accepts the requirements-satisfied execution result only for "
            "preparing a separate source-map closure adjudication packet. It does "
            "not claim or register source-map closure, close the QFT-GR seam, move "
            "tranche 004, assemble release, mark readiness, discharge theorem/proof "
            "debt or retained assumptions, authorize Phase 2, authorize empirical "
            "validation, authorize publication, promote the master action, or make "
            "an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_source_map_authorization_adjudication_result_review(
    *,
    adjudication_execution_path: Path = DEFAULT_ADJUDICATION_EXECUTION_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_source_map_authorization_adjudication_result_review(
        adjudication_execution_path=adjudication_execution_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha retained tranche 004 source-map authorization "
            "adjudication result review."
        )
    )
    parser.add_argument(
        "--adjudication-execution",
        type=Path,
        default=DEFAULT_ADJUDICATION_EXECUTION_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    adjudication_execution_path = (
        ns.adjudication_execution
        if ns.adjudication_execution.is_absolute()
        else (REPO_ROOT / ns.adjudication_execution)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_source_map_authorization_adjudication_result_review(
        adjudication_execution_path=adjudication_execution_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_source_map_authorization_adjudication_result_review_report: "
        f"accepted={payload['accepted']} classification={payload['result_review_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
