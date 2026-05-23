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
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_witness_chain_construction_from_research_candidate_report import (
    ASSEMBLE_RELEASE_PACKET_TARGET,
    CONSTRUCTION_RESULT_CLASSIFICATION as EXPECTED_CONSTRUCTION_RESULT_CLASSIFICATION,
    DEFAULT_OUT as DEFAULT_CONSTRUCTION_EXECUTION_PATH,
    OUTCOME_ID as EXPECTED_CONSTRUCTION_EXECUTION_OUTCOME,
    SCHEMA_ID as EXPECTED_CONSTRUCTION_EXECUTION_SCHEMA_ID,
    ATTEMPT_ID as EXPECTED_CONSTRUCTION_EXECUTION_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_"
    "RESULT_REVIEW_20260523_v0"
)
REVIEW_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_"
    "RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_RESULT_"
    "REVIEW_ACCEPTS_WITNESS_CHAIN_CONSTRUCTION_AND_AUTHORIZES_SOURCE_MAP_"
    "AUTHORIZATION_ADJUDICATION_PACKET_PREPARATION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "witness_chain_construction_accepted_source_map_authorization_adjudication_packet_"
    "preparation_only"
)
CONSUMED_TARGET = (
    "review_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_"
    "from_research_candidate_result"
)
NEXT_TARGET = "prepare_v01_alpha_retained_tranche_004_source_map_authorization_adjudication_packet"
ADJUDICATION_EXECUTION_TARGET = (
    "execute_v01_alpha_retained_tranche_004_source_map_authorization_adjudication"
)
ADJUDICATION_RESULT_REVIEW_TARGET = (
    "review_v01_alpha_retained_tranche_004_source_map_authorization_adjudication_result"
)
REFINED_CONSTRUCTION_TARGET = (
    "prepare_refined_v01_alpha_retained_tranche_004_source_map_witness_chain_"
    "construction_packet_from_research_candidate"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_RESULT_REVIEW_20260523_v0.json"
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
    "source_map_authorization_adjudication_executed",
    "source_map_authorization_adjudication_packet_prepared",
    "source_map_closure_achieved",
    "source_map_closure_authorized",
    "source_map_closure_claimed",
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


def _reviewed_components(construction: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "component_id": row.get("component_id"),
            "candidate_surface": row.get("candidate_surface"),
            "candidate_result_review_surface": row.get("candidate_result_review_surface"),
            "construction_status": row.get("construction_status"),
            "review_status": "accepted_for_source_map_authorization_adjudication_input",
            "closure_status": "not_adjudicated_not_closure_evidence_by_review_alone",
        }
        for row in construction.get("constructed_witness_chain_components", [])
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The construction is accepted as witness-chain construction only; "
                "the next narrow question is whether it satisfies source-map "
                "semantic-closure authorization requirements."
            ),
        },
        {
            "target": ADJUDICATION_EXECUTION_TARGET,
            "decision": "deferred",
            "reason": "Adjudication execution requires a prepared adjudication packet first.",
        },
        {
            "target": ADJUDICATION_RESULT_REVIEW_TARGET,
            "decision": "deferred",
            "reason": "Adjudication result review is available only after adjudication execution.",
        },
        {
            "target": REFINED_CONSTRUCTION_TARGET,
            "decision": "deferred",
            "reason": "Refinement remains available if adjudication-packet preparation rejects the review input.",
        },
        {
            "target": ASSEMBLE_RELEASE_PACKET_TARGET,
            "decision": "not_authorized",
            "reason": "Release assembly remains blocked by retained tranche 004.",
        },
    ]


def build_construction_result_review(
    *,
    construction_path: Path = DEFAULT_CONSTRUCTION_EXECUTION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    construction = _read_json(construction_path)
    candidate_components = list(construction.get("candidate_witness_chain_components", []))
    constructed_components = list(construction.get("constructed_witness_chain_components", []))
    reviewed_components = _reviewed_components(construction)
    required_proof_surfaces = list(construction.get("required_proof_surfaces", []))
    required_evidence_surfaces = list(construction.get("required_evidence_surfaces", []))
    success_criteria = list(construction.get("success_criteria", []))
    failure_criteria = list(construction.get("failure_criteria", []))
    construction_boundary = list(construction.get("construction_execution_boundary", []))
    candidate_next_targets = _candidate_next_targets()
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_construction_execution": construction.get("attempt_id")
        == EXPECTED_CONSTRUCTION_EXECUTION_ID,
        "construction_execution_schema_expected": construction.get("schema_id")
        == EXPECTED_CONSTRUCTION_EXECUTION_SCHEMA_ID,
        "construction_execution_outcome_expected": construction.get("outcome_id")
        == EXPECTED_CONSTRUCTION_EXECUTION_OUTCOME,
        "construction_execution_selected_this_review": construction.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "construction_execution_was_bounded_and_accepted": construction.get(
            "accepted"
        )
        is True
        and construction.get("executed") is True
        and construction.get("bounded_construction_execution_only") is True
        and construction.get("source_map_witness_chain_construction_executed") is True,
        "classification_is_expected_pending_review": construction.get(
            "construction_result_classification"
        )
        == EXPECTED_CONSTRUCTION_RESULT_CLASSIFICATION
        and construction.get("construction_result_classification_count") == 1
        and construction.get("witness_chain_constructed_pending_result_review") is True,
        "constructed_component_chain_reviewable": len(candidate_components) == 7
        and construction.get("candidate_witness_chain_component_count") == 7
        and len(constructed_components) == 7
        and construction.get("constructed_witness_chain_component_count") == 7
        and construction.get("required_witness_chain_component_count") == 7
        and all(
            row.get("construction_status")
            == "constructed_candidate_pending_result_review"
            for row in constructed_components
        )
        and all(row.get("review_required_before_closure") is True for row in constructed_components),
        "review_accepts_constructed_chain_for_adjudication_input_only": len(
            reviewed_components
        )
        == 7
        and all(
            row.get("review_status")
            == "accepted_for_source_map_authorization_adjudication_input"
            for row in reviewed_components
        ),
        "proof_evidence_and_boundaries_carried": len(required_proof_surfaces) == 7
        and construction.get("required_proof_surface_count") == 7
        and len(required_evidence_surfaces) == 6
        and construction.get("required_evidence_surface_count") == 6
        and len(success_criteria) == 4
        and construction.get("success_criteria_count") == 4
        and len(failure_criteria) == 5
        and construction.get("failure_criteria_count") == 5
        and len(construction_boundary) == 5
        and construction.get("construction_execution_boundary_count") == 5,
        "tranche_004_retained": construction.get("tranche_004_status")
        == TRANCHE_004_STATUS
        and construction.get("retained_tranche_004_carry_forward", {}).get("status")
        == TRANCHE_004_STATUS
        and construction.get("selected_remediation_finding_id") == TRANCHE_004_FINDING_ID
        and construction.get("selected_dependency") == TRANCHE_004_DEPENDENCY,
        "documented_dependency_nonblocking_queue_preserved": construction.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS
        and construction.get("tranche_002_status") == TRANCHE_002_STATUS
        and construction.get("tranche_003_status") == TRANCHE_003_STATUS
        and construction.get("tranche_005_status") == TRANCHE_005_STATUS
        and construction.get("tranche_005_dependency") == TRANCHE_005_DEPENDENCY
        and construction.get("tranche_006_status") == TRANCHE_006_STATUS
        and construction.get("tranche_006_dependency") == TRANCHE_006_DEPENDENCY
        and construction.get("tranche_006_dependency_class") == TRANCHE_006_DEPENDENCY_CLASS
        and construction.get("tranche_006_dependency_finding_id")
        == TRANCHE_006_FINDING_ID
        and construction.get("documented_dependency_nonblocking_tranche_count") == 5,
        "release_hold_preserved": construction.get("release_readiness_decision_status")
        == RELEASE_READINESS_DECISION
        and construction.get("release_readiness_held") is True
        and construction.get("release_readiness_still_blocked") is True
        and construction.get("release_readiness_proceed_authorized") is False,
        "no_closure_seam_or_blocker_movement_in_input": construction.get(
            "source_map_closure_claimed"
        )
        is False
        and construction.get("source_map_closure_authorized") is False
        and construction.get("qft_gr_seam_closed") is False
        and construction.get("qft_gr_seam_closure_authorized") is False
        and construction.get("tranche_004_status_moved") is False
        and construction.get("tranche_004_retained_blocker_discharged") is False,
        "no_release_theorem_phase_empirical_publication_or_master_promotion": construction.get(
            "release_assembly_authorized"
        )
        is False
        and construction.get("release_packet_assembled") is False
        and construction.get("lean_theorem_debt_discharged") is False
        and construction.get("proof_debt_reduced") is False
        and construction.get("phase2_authorized") is False
        and construction.get("empirical_validation_authorized") is False
        and construction.get("publication_authorized") is False
        and construction.get("master_action_promotion_authorized") is False,
        "adjudication_packet_preparation_selected_only": sum(
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
        else "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_RESULT_REVIEW_BLOCKED",
        "consumes_construction_execution": EXPECTED_CONSTRUCTION_EXECUTION_ID,
        "consumes_construction_execution_pointer": _ptr(construction_path),
        "consumed_construction_execution_schema_id": construction.get("schema_id"),
        "consumed_construction_execution_outcome_id": construction.get("outcome_id"),
        "review_scope": (
            "REVIEW_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_FROM_"
            "RESEARCH_CANDIDATE_RESULT_ONLY_NO_SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_OR_"
            "RELEASE_PROMOTION"
        ),
        "construction_result_reviewed": accepted,
        "construction_result_accepted": accepted,
        "witness_chain_construction_accepted": accepted,
        "source_map_witness_chain_construction_accepted": accepted,
        "witness_chain_constructed_accepted_by_review": accepted,
        "source_map_witness_chain_constructed_accepted_by_review": accepted,
        "accepted_for_source_map_authorization_adjudication_packet_preparation_only": accepted,
        "source_map_authorization_adjudication_packet_preparation_authorized": accepted,
        "source_map_authorization_adjudication_packet_preparation_only": accepted,
        "source_map_authorization_adjudication_packet_prepared": False,
        "source_map_authorization_adjudication_execution_authorized": False,
        "source_map_authorization_adjudication_executed": False,
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "result_classification_count": 1 if accepted else 0,
        "consumed_construction_result_classification": construction.get(
            "construction_result_classification"
        ),
        "consumed_witness_chain_constructed_pending_result_review": construction.get(
            "witness_chain_constructed_pending_result_review"
        )
        is True,
        "candidate_witness_chain_components": candidate_components,
        "candidate_witness_chain_component_count": len(candidate_components),
        "constructed_witness_chain_components": constructed_components,
        "constructed_witness_chain_component_count": len(constructed_components),
        "reviewed_witness_chain_components": reviewed_components,
        "reviewed_witness_chain_component_count": len(reviewed_components),
        "accepted_witness_chain_component_count": len(reviewed_components)
        if accepted
        else 0,
        "required_witness_chain_component_count": construction.get(
            "required_witness_chain_component_count"
        ),
        "required_proof_surfaces": required_proof_surfaces,
        "required_proof_surface_count": len(required_proof_surfaces),
        "required_evidence_surfaces": required_evidence_surfaces,
        "required_evidence_surface_count": len(required_evidence_surfaces),
        "success_criteria": success_criteria,
        "success_criteria_count": len(success_criteria),
        "failure_criteria": failure_criteria,
        "failure_criteria_count": len(failure_criteria),
        "construction_execution_boundary": construction_boundary,
        "construction_execution_boundary_count": len(construction_boundary),
        "witness_chain_constructed": accepted,
        "source_map_witness_chain_constructed": accepted,
        "witness_chain_constructed_claimed": accepted,
        "source_map_witness_chain_constructed_claimed": accepted,
        "source_map_closure_requirements_adjudicated": False,
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
        "retained_tranche_004_carry_forward": construction.get(
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
        else "REMEDIATE_V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_RESULT_REVIEW",
        "selected_next_target_kind": (
            "retained_tranche_004_source_map_authorization_adjudication_packet_"
            "preparation_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_"
            "PACKET_ONLY_NO_ADJUDICATION_EXECUTION_SOURCE_MAP_CLOSURE_BLOCKER_"
            "MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "adjudication_question": (
            "Does the accepted witness chain satisfy the source-map semantic-closure "
            "authorization requirements?"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained tranche 004 source-map witness-chain construction result "
            "review accepts the constructed witness chain only as input for a future "
            "source-map authorization adjudication packet. It does not prepare or "
            "execute adjudication, claim source-map closure, close the QFT-GR seam, "
            "move tranche 004, assemble release, mark readiness, discharge theorem/"
            "proof debt or retained assumptions, authorize Phase 2, authorize "
            "empirical validation, authorize publication, promote the master action, "
            "or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_construction_result_review(
    *,
    construction_path: Path = DEFAULT_CONSTRUCTION_EXECUTION_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_construction_result_review(
        construction_path=construction_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha retained tranche 004 source-map witness-chain "
            "construction result review."
        )
    )
    parser.add_argument(
        "--construction",
        type=Path,
        default=DEFAULT_CONSTRUCTION_EXECUTION_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    construction_path = (
        ns.construction
        if ns.construction.is_absolute()
        else (REPO_ROOT / ns.construction)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_construction_result_review(
        construction_path=construction_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_source_map_witness_chain_construction_result_review_report: "
        f"accepted={payload['accepted']} classification={payload['result_review_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
