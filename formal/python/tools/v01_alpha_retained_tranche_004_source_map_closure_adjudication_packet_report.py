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
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_authorization_adjudication_result_review_report import (
    ASSEMBLE_RELEASE_PACKET_TARGET,
    DEFAULT_OUT as DEFAULT_AUTHORIZATION_RESULT_REVIEW_PATH,
    OUTCOME_ID as EXPECTED_AUTHORIZATION_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_AUTHORIZATION_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_AUTHORIZATION_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_AUTHORIZATION_RESULT_REVIEW_SCHEMA_ID,
    SOURCE_MAP_CLOSURE_ADJUDICATION_EXECUTION_TARGET,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_PACKET_"
    "20260523_v0"
)
PACKET_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_PACKET_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_PACKET_"
    "PREPARED_WITH_NO_SOURCE_MAP_CLOSURE_OR_RELEASE_PROMOTION"
)
PACKET_CLASSIFICATION = (
    "source_map_closure_adjudication_packet_prepared_no_source_map_closure_or_"
    "release_promotion"
)
CONSUMED_TARGET = (
    "prepare_v01_alpha_retained_tranche_004_source_map_closure_adjudication_packet"
)
NEXT_TARGET = (
    "review_v01_alpha_retained_tranche_004_source_map_closure_adjudication_"
    "packet_result"
)
REFINED_AUTHORIZATION_ADJUDICATION_TARGET = (
    "prepare_refined_v01_alpha_retained_tranche_004_source_map_authorization_"
    "adjudication_packet"
)
BLOCKER_MOVEMENT_ADJUDICATION_TARGET = (
    "prepare_v01_alpha_retained_tranche_004_blocker_movement_adjudication_packet"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_PACKET_20260523_v0.json"
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
    "source_map_closure_adjudication_execution_authorized",
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


def _closure_adjudication_requirements(review: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for row in review.get("reviewed_authorization_requirements", []):
        rows.append(
            {
                "requirement_id": row.get("requirement_id"),
                "component_id": row.get("component_id"),
                "candidate_surface": row.get("candidate_surface"),
                "candidate_result_review_surface": row.get(
                    "candidate_result_review_surface"
                ),
                "input_result_review_status": row.get("result_review_status"),
                "input_closure_status": row.get("closure_status"),
                "required_closure_adjudication": (
                    "Determine whether this accepted authorization requirement can "
                    "support source-map closure under the repo's release-control "
                    "rules or must remain retained/refined."
                ),
                "packet_status": "prepared_for_future_closure_adjudication_not_answered",
            }
        )
    return rows


def _closure_adjudication_success_criteria() -> list[dict[str, str]]:
    return [
        {
            "criterion_id": "all_accepted_authorization_requirements_checked",
            "criterion": (
                "Every accepted source-map authorization requirement is explicitly "
                "checked for closure eligibility under release-control rules."
            ),
        },
        {
            "criterion_id": "closure_decision_requires_execution_and_review",
            "criterion": (
                "Any source-map closure decision is deferred to bounded closure "
                "adjudication execution and a separate result review."
            ),
        },
        {
            "criterion_id": "blocker_movement_separate_from_closure_packet",
            "criterion": (
                "Tranche 004 movement remains separate from packet preparation and "
                "requires later governed authorization."
            ),
        },
        {
            "criterion_id": "release_hold_survives_packet",
            "criterion": "Release readiness remains held and release assembly remains unauthorized.",
        },
    ]


def _closure_adjudication_failure_criteria() -> list[dict[str, str]]:
    return [
        {
            "criterion_id": "authorization_requirement_rejected_for_closure",
            "condition": (
                "An accepted source-map authorization requirement does not support "
                "source-map closure eligibility."
            ),
            "required_result": "source_map_closure_not_authorized_retained_blocker_continues",
        },
        {
            "criterion_id": "closure_adjudication_treated_as_closure_by_preparation",
            "condition": "Packet preparation is treated as a source-map closure decision.",
            "required_result": "reject_closure_claim_no_status_movement",
        },
        {
            "criterion_id": "qft_gr_seam_closure_inferred",
            "condition": "QFT-GR seam closure is inferred from source-map packet preparation.",
            "required_result": "qft_gr_seam_remains_open",
        },
        {
            "criterion_id": "release_or_blocker_movement_requested",
            "condition": (
                "Release assembly, readiness marking, or tranche 004 movement is "
                "requested before closure adjudication execution and result review."
            ),
            "required_result": "release_hold_continues",
        },
    ]


def _closure_adjudication_execution_boundary() -> list[dict[str, str]]:
    return [
        {
            "boundary_id": "packet_preparation_only",
            "rule": "This packet prepares closure adjudication scope; it does not execute closure adjudication.",
        },
        {
            "boundary_id": "review_before_execution",
            "rule": "The prepared packet must be reviewed before closure adjudication execution can be authorized.",
        },
        {
            "boundary_id": "closure_question_not_answered_by_packet",
            "rule": (
                "The packet asks whether source-map closure can be adjudicated under "
                "release-control rules; it does not answer that question."
            ),
        },
        {
            "boundary_id": "no_source_map_closure_by_preparation",
            "rule": "Source-map closure remains unclaimed, unauthorized, and unregistered.",
        },
        {
            "boundary_id": "release_lane_stays_held",
            "rule": "Release readiness remains held and release assembly remains unauthorized.",
        },
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The prepared source-map closure adjudication packet requires result "
                "review before closure adjudication execution can be authorized."
            ),
        },
        {
            "target": SOURCE_MAP_CLOSURE_ADJUDICATION_EXECUTION_TARGET,
            "decision": "deferred",
            "reason": "Execution requires packet result review first.",
        },
        {
            "target": BLOCKER_MOVEMENT_ADJUDICATION_TARGET,
            "decision": "deferred",
            "reason": (
                "Blocker movement remains unavailable unless a later closure "
                "adjudication execution and result review authorize it."
            ),
        },
        {
            "target": REFINED_AUTHORIZATION_ADJUDICATION_TARGET,
            "decision": "deferred",
            "reason": "Refinement remains available if packet review rejects the closure adjudication scope.",
        },
        {
            "target": ASSEMBLE_RELEASE_PACKET_TARGET,
            "decision": "not_authorized",
            "reason": "Release assembly remains blocked by retained tranche 004.",
        },
    ]


def build_source_map_closure_adjudication_packet(
    *,
    review_path: Path = DEFAULT_AUTHORIZATION_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(review_path)
    closure_requirements = _closure_adjudication_requirements(review)
    success_criteria = _closure_adjudication_success_criteria()
    failure_criteria = _closure_adjudication_failure_criteria()
    execution_boundary = _closure_adjudication_execution_boundary()
    candidate_next_targets = _candidate_next_targets()
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_source_map_authorization_result_review": review.get(
            "review_id"
        )
        == EXPECTED_AUTHORIZATION_RESULT_REVIEW_ID,
        "authorization_result_review_schema_expected": review.get("schema_id")
        == EXPECTED_AUTHORIZATION_RESULT_REVIEW_SCHEMA_ID,
        "authorization_result_review_outcome_expected": review.get("outcome_id")
        == EXPECTED_AUTHORIZATION_RESULT_REVIEW_OUTCOME,
        "authorization_result_review_selected_this_packet": review.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "authorization_requirements_accepted_for_packet_preparation_only": review.get(
            "accepted"
        )
        is True
        and review.get("source_map_authorization_adjudication_result_reviewed") is True
        and review.get("source_map_authorization_adjudication_result_accepted") is True
        and review.get(
            "source_map_authorization_requirements_satisfied_accepted_by_review"
        )
        is True
        and review.get(
            "source_map_authorization_requirements_satisfied_accepted_for_closure_adjudication_packet_preparation_only"
        )
        is True
        and review.get("result_review_classification")
        == EXPECTED_AUTHORIZATION_RESULT_REVIEW_CLASSIFICATION,
        "source_map_closure_not_authorized_by_input_review": review.get(
            "source_map_authorization_result_accepted_as_closure_evidence"
        )
        is False
        and review.get("source_map_closure_adjudication_packet_preparation_only")
        is True
        and review.get("source_map_closure_adjudication_packet_prepared") is False
        and review.get("source_map_closure_authorized") is False
        and review.get("source_map_closure_claimed") is False
        and review.get("source_map_closure_registered") is False,
        "closure_requirements_prepared_from_accepted_authorization_requirements": len(
            closure_requirements
        )
        == 7
        and review.get("accepted_authorization_requirement_count") == 7
        and review.get("reviewed_authorization_requirement_count") == 7
        and all(
            row["packet_status"]
            == "prepared_for_future_closure_adjudication_not_answered"
            for row in closure_requirements
        ),
        "proof_evidence_and_boundaries_carried": review.get(
            "required_proof_surface_count"
        )
        == 7
        and review.get("required_evidence_surface_count") == 6
        and len(success_criteria) == 4
        and len(failure_criteria) == 4
        and len(execution_boundary) == 5,
        "tranche_004_retained": review.get("tranche_004_status") == TRANCHE_004_STATUS
        and review.get("retained_tranche_004_carry_forward", {}).get("status")
        == TRANCHE_004_STATUS
        and review.get("selected_remediation_finding_id") == TRANCHE_004_FINDING_ID
        and review.get("selected_dependency") == TRANCHE_004_DEPENDENCY,
        "documented_dependency_nonblocking_queue_preserved": review.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS
        and review.get("tranche_002_status") == TRANCHE_002_STATUS
        and review.get("tranche_003_status") == TRANCHE_003_STATUS
        and review.get("tranche_005_status") == TRANCHE_005_STATUS
        and review.get("tranche_005_dependency") == TRANCHE_005_DEPENDENCY
        and review.get("tranche_006_status") == TRANCHE_006_STATUS
        and review.get("tranche_006_dependency") == TRANCHE_006_DEPENDENCY
        and review.get("tranche_006_dependency_class") == TRANCHE_006_DEPENDENCY_CLASS
        and review.get("tranche_006_dependency_finding_id") == TRANCHE_006_FINDING_ID
        and review.get("documented_dependency_nonblocking_tranche_count") == 5,
        "release_hold_preserved": review.get("release_readiness_decision_status")
        == RELEASE_READINESS_DECISION
        and review.get("release_readiness_held") is True
        and review.get("release_readiness_still_blocked") is True
        and review.get("release_readiness_proceed_authorized") is False,
        "no_closure_seam_or_blocker_movement_in_input": review.get(
            "source_map_closure_authorized"
        )
        is False
        and review.get("source_map_closure_claimed") is False
        and review.get("source_map_closure_registered") is False
        and review.get("qft_gr_seam_closed") is False
        and review.get("qft_gr_seam_closure_authorized") is False
        and review.get("tranche_004_status_moved") is False
        and review.get("tranche_004_retained_blocker_discharged") is False,
        "no_release_theorem_phase_empirical_publication_or_master_promotion": review.get(
            "release_assembly_authorized"
        )
        is False
        and review.get("release_packet_assembled") is False
        and review.get("lean_theorem_debt_discharged") is False
        and review.get("proof_debt_reduced") is False
        and review.get("phase2_authorized") is False
        and review.get("empirical_validation_authorized") is False
        and review.get("publication_authorized") is False
        and review.get("master_action_promotion_authorized") is False,
        "packet_review_selected_only": sum(
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
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "prepared": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_"
            "PACKET_BLOCKED"
        ),
        "consumes_source_map_authorization_adjudication_result_review": (
            EXPECTED_AUTHORIZATION_RESULT_REVIEW_ID
        ),
        "consumes_source_map_authorization_adjudication_result_review_pointer": _ptr(
            review_path
        ),
        "consumed_source_map_authorization_adjudication_result_review_schema_id": (
            review.get("schema_id")
        ),
        "consumed_source_map_authorization_adjudication_result_review_outcome_id": (
            review.get("outcome_id")
        ),
        "consumed_source_map_authorization_adjudication_result_review_classification": (
            review.get("result_review_classification")
        ),
        "packet_scope": (
            "PREPARE_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_"
            "PACKET_ONLY_NO_SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if accepted else 0,
        "source_map_closure_adjudication_packet_prepared": accepted,
        "source_map_closure_adjudication_packet_preparation_only": accepted,
        "source_map_closure_adjudication_question_prepared": accepted,
        "source_map_closure_adjudication_question_answered": False,
        "source_map_closure_adjudication_execution_authorized_by_packet": False,
        "source_map_closure_adjudication_execution_authorized": False,
        "source_map_closure_adjudication_executed": False,
        "source_map_closure_adjudication_result_review_authorized": False,
        "closure_adjudication_question": (
            "Given that source-map authorization requirements were accepted, can "
            "source-map closure be adjudicated under the repo's release-control rules?"
        ),
        "closure_adjudication_requirements": closure_requirements,
        "closure_adjudication_requirement_count": len(closure_requirements),
        "accepted_authorization_requirement_count": review.get(
            "accepted_authorization_requirement_count"
        ),
        "reviewed_authorization_requirements": review.get(
            "reviewed_authorization_requirements", []
        ),
        "reviewed_authorization_requirement_count": review.get(
            "reviewed_authorization_requirement_count"
        ),
        "reviewed_witness_chain_components": review.get(
            "reviewed_witness_chain_components", []
        ),
        "reviewed_witness_chain_component_count": review.get(
            "reviewed_witness_chain_component_count"
        ),
        "required_proof_surfaces": review.get("required_proof_surfaces", []),
        "required_proof_surface_count": review.get("required_proof_surface_count"),
        "required_evidence_surfaces": review.get("required_evidence_surfaces", []),
        "required_evidence_surface_count": review.get("required_evidence_surface_count"),
        "closure_adjudication_success_criteria": success_criteria,
        "closure_adjudication_success_criteria_count": len(success_criteria),
        "closure_adjudication_failure_criteria": failure_criteria,
        "closure_adjudication_failure_criteria_count": len(failure_criteria),
        "closure_adjudication_execution_boundary": execution_boundary,
        "closure_adjudication_execution_boundary_count": len(execution_boundary),
        "source_map_authorization_adjudication_result_reviewed": True
        if accepted
        else False,
        "source_map_authorization_adjudication_result_accepted": True
        if accepted
        else False,
        "requirements_satisfied_status_accepted_by_review": True if accepted else False,
        "source_map_authorization_requirements_satisfied_accepted_by_review": True
        if accepted
        else False,
        "source_map_authorization_requirements_satisfied_accepted_for_closure_adjudication_packet_preparation_only": True
        if accepted
        else False,
        "source_map_authorization_result_accepted_as_closure_evidence": False,
        "source_map_closure_requirements_adjudicated": review.get(
            "source_map_closure_requirements_adjudicated"
        )
        is True,
        "source_map_closure_authorization_requirements_decision_recorded": review.get(
            "source_map_closure_authorization_requirements_decision_recorded"
        )
        is True,
        "source_map_closure_authorization_decision_accepted_by_review": False,
        "source_map_closure_authorization_result_review_required": False,
        "witness_chain_construction_accepted": True if accepted else False,
        "source_map_witness_chain_construction_accepted": True if accepted else False,
        "witness_chain_constructed": True if accepted else False,
        "source_map_witness_chain_constructed": True if accepted else False,
        "witness_chain_constructed_claimed": True if accepted else False,
        "source_map_witness_chain_constructed_claimed": True if accepted else False,
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
        "retained_tranche_004_carry_forward": review.get(
            "retained_tranche_004_carry_forward", {}
        ),
        "required_future_route_for_tranche_004": TRANCHE_004_FUTURE_ROUTE,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "tranche_004_status_moved_by_packet": False,
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
            "REMEDIATE_V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_"
            "ADJUDICATION_PACKET"
        ),
        "selected_next_target_kind": (
            "retained_tranche_004_source_map_closure_adjudication_packet_"
            "result_review_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_"
            "PACKET_RESULT_ONLY_NO_SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_"
            "PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained tranche 004 source-map closure adjudication packet asks "
            "whether source-map closure can be adjudicated under the repo's "
            "release-control rules. It does not answer that question, execute "
            "closure adjudication, claim or register source-map closure, close the "
            "QFT-GR seam, move tranche 004, assemble release, mark readiness, "
            "discharge theorem/proof debt or retained assumptions, authorize Phase "
            "2, authorize empirical validation, authorize publication, promote the "
            "master action, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_source_map_closure_adjudication_packet(
    *,
    review_path: Path = DEFAULT_AUTHORIZATION_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_source_map_closure_adjudication_packet(
        review_path=review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha retained tranche 004 source-map closure "
            "adjudication packet."
        )
    )
    parser.add_argument(
        "--review",
        type=Path,
        default=DEFAULT_AUTHORIZATION_RESULT_REVIEW_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    review_path = ns.review if ns.review.is_absolute() else (REPO_ROOT / ns.review)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_source_map_closure_adjudication_packet(
        review_path=review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_source_map_closure_adjudication_packet_report: "
        f"accepted={payload['accepted']} classification={payload['packet_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
