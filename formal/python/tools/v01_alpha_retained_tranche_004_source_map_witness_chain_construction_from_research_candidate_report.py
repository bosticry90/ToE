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
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate_result_review_report import (
    ASSEMBLE_RELEASE_PACKET_TARGET,
    DEFAULT_OUT as DEFAULT_CONSTRUCTION_PACKET_RESULT_REVIEW_PATH,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    POST_CONSTRUCTION_RESULT_REVIEW_TARGET as NEXT_TARGET,
    REFINED_RESEARCH_TARGET,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_"
    "FROM_RESEARCH_CANDIDATE_20260523_v0"
)
ATTEMPT_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_"
    "FROM_RESEARCH_CANDIDATE_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_FROM_"
    "RESEARCH_CANDIDATE_EXECUTED_WITH_NO_SOURCE_MAP_CLOSURE_OR_RELEASE_PROMOTION"
)
CONSTRUCTION_RESULT_CLASSIFICATION = "witness_chain_constructed_pending_result_review"
CONSTRUCTION_TARGET = (
    "construct_repo_local_source_map_witness_chain_for_retained_tranche_004_from_"
    "accepted_partial_research_candidate"
)
EXECUTION_TARGET = (
    "execute_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_"
    "from_research_candidate"
)
SOURCE_MAP_ADJUDICATION_TARGET = (
    "prepare_v01_alpha_retained_tranche_004_source_map_authorization_adjudication_"
    "packet_from_reviewed_witness_chain"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_FROM_RESEARCH_CANDIDATE_20260523_v0.json"
)

FORBIDDEN_EFFECTS = [
    "axiom_spec_backed_debt_reduced",
    "blocker_movement_authorized",
    "blocker_movement_registered",
    "construction_result_claimed",
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
    "source_map_closure_authorized",
    "source_map_closure_claimed",
    "source_map_witness_chain_constructed_claimed",
    "tranche_004_retained_blocker_discharged",
    "tranche_004_status_moved",
    "unbounded_construction_execution_authorized",
    "v01_alpha_marked_ready",
    "witness_chain_constructed_claimed",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _constructed_components(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "component_id": row.get("component_id"),
            "candidate_surface": row.get("candidate_surface"),
            "candidate_result_review_surface": row.get("candidate_result_review_surface"),
            "input_status": row.get("input_status"),
            "construction_status": "constructed_candidate_pending_result_review",
            "review_required_before_closure": True,
        }
        for row in result_review.get("candidate_witness_chain_components", [])
    ]


def _execution_steps(constructed_components: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        {
            "step_id": "construction_001_bind_accepted_result_review_authorization",
            "result": "bounded_construction_execution_authorization_consumed",
        },
        {
            "step_id": "construction_002_carry_candidate_component_set",
            "result": "seven_candidate_components_carried",
            "component_count": len(constructed_components),
        },
        {
            "step_id": "construction_003_construct_candidate_witness_chain_ordering",
            "result": "candidate_witness_chain_constructed_pending_result_review",
            "constructed_component_ids": [
                str(row["component_id"]) for row in constructed_components
            ],
        },
        {
            "step_id": "construction_004_preserve_closure_and_release_firewall",
            "result": "no_source_map_closure_blocker_movement_or_release_promotion",
        },
        {
            "step_id": "construction_005_classify_result_pending_review",
            "result": CONSTRUCTION_RESULT_CLASSIFICATION,
            "selected_next_target": NEXT_TARGET,
        },
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The bounded construction execution recorded one conservative result "
                "classification and must be reviewed before any closure or status "
                "adjudication."
            ),
        },
        {
            "target": SOURCE_MAP_ADJUDICATION_TARGET,
            "decision": "deferred",
            "reason": (
                "Source-map authorization adjudication requires a separate accepted "
                "construction result review."
            ),
        },
        {
            "target": REFINED_RESEARCH_TARGET,
            "decision": "deferred",
            "reason": "Refined research remains available if the execution result review rejects the chain.",
        },
        {
            "target": ASSEMBLE_RELEASE_PACKET_TARGET,
            "decision": "not_authorized",
            "reason": "Release assembly remains blocked by retained tranche 004.",
        },
    ]


def build_construction_execution(
    *,
    result_review_path: Path = DEFAULT_CONSTRUCTION_PACKET_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    candidate_components = list(result_review.get("candidate_witness_chain_components", []))
    constructed_components = _constructed_components(result_review)
    required_proof_surfaces = list(result_review.get("required_proof_surfaces", []))
    required_evidence_surfaces = list(result_review.get("required_evidence_surfaces", []))
    success_criteria = list(result_review.get("success_criteria", []))
    failure_criteria = list(result_review.get("failure_criteria", []))
    construction_boundary = list(result_review.get("construction_execution_boundary", []))
    execution_steps = _execution_steps(constructed_components)
    candidate_next_targets = _candidate_next_targets()
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_construction_packet_result_review": result_review.get(
            "review_id"
        )
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_schema_expected": result_review.get("schema_id")
        == EXPECTED_RESULT_REVIEW_SCHEMA_ID,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_selected_this_execution": result_review.get(
            "selected_next_target"
        )
        == EXECUTION_TARGET,
        "result_review_authorizes_bounded_execution_only": result_review.get(
            "accepted"
        )
        is True
        and result_review.get("result_review_classification")
        == EXPECTED_RESULT_REVIEW_CLASSIFICATION
        and result_review.get("bounded_construction_execution_authorized_by_review")
        is True
        and result_review.get(
            "source_map_witness_chain_construction_execution_authorized_by_review"
        )
        is True,
        "input_partial_candidate_classification_preserved": result_review.get(
            "accepted_input_classification"
        )
        == "partial_witness_chain_candidate_accepted_for_construction_packet_preparation_only",
        "input_packet_prepared_but_not_executed": result_review.get(
            "construction_packet_prepared"
        )
        is True
        and result_review.get("construction_packet_prepared_only") is True
        and result_review.get("source_map_witness_chain_construction_executed")
        is False
        and result_review.get("witness_chain_constructed") is False
        and result_review.get("source_map_witness_chain_constructed") is False,
        "candidate_material_carried": len(candidate_components) == 7
        and result_review.get("candidate_witness_chain_component_count") == 7
        and len(required_proof_surfaces) == 7
        and result_review.get("required_proof_surface_count") == 7
        and len(required_evidence_surfaces) == 6
        and result_review.get("required_evidence_surface_count") == 6,
        "criteria_and_boundaries_carried": len(success_criteria) == 4
        and result_review.get("success_criteria_count") == 4
        and len(failure_criteria) == 5
        and result_review.get("failure_criteria_count") == 5
        and len(construction_boundary) == 5
        and result_review.get("construction_execution_boundary_count") == 5,
        "bounded_construction_executed_with_exactly_one_classification": len(
            execution_steps
        )
        == 5
        and CONSTRUCTION_RESULT_CLASSIFICATION
        == "witness_chain_constructed_pending_result_review",
        "constructed_components_pending_review": len(constructed_components) == 7
        and all(
            row.get("construction_status")
            == "constructed_candidate_pending_result_review"
            for row in constructed_components
        )
        and all(row.get("review_required_before_closure") is True for row in constructed_components),
        "tranche_004_retained": result_review.get("tranche_004_status")
        == TRANCHE_004_STATUS
        and result_review.get("retained_tranche_004_carry_forward", {}).get("status")
        == TRANCHE_004_STATUS
        and result_review.get("selected_remediation_finding_id") == TRANCHE_004_FINDING_ID
        and result_review.get("selected_dependency") == TRANCHE_004_DEPENDENCY,
        "documented_dependency_nonblocking_queue_preserved": result_review.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS
        and result_review.get("tranche_002_status") == TRANCHE_002_STATUS
        and result_review.get("tranche_003_status") == TRANCHE_003_STATUS
        and result_review.get("tranche_005_status") == TRANCHE_005_STATUS
        and result_review.get("tranche_005_dependency") == TRANCHE_005_DEPENDENCY
        and result_review.get("tranche_006_status") == TRANCHE_006_STATUS
        and result_review.get("tranche_006_dependency") == TRANCHE_006_DEPENDENCY
        and result_review.get("tranche_006_dependency_class") == TRANCHE_006_DEPENDENCY_CLASS
        and result_review.get("tranche_006_dependency_finding_id")
        == TRANCHE_006_FINDING_ID
        and result_review.get("documented_dependency_nonblocking_tranche_count") == 5,
        "release_hold_preserved": result_review.get("release_readiness_decision_status")
        == RELEASE_READINESS_DECISION
        and result_review.get("release_readiness_held") is True
        and result_review.get("release_readiness_still_blocked") is True
        and result_review.get("release_readiness_proceed_authorized") is False,
        "no_closure_seam_or_blocker_movement_in_input": result_review.get(
            "source_map_closure_claimed"
        )
        is False
        and result_review.get("source_map_closure_authorized") is False
        and result_review.get("qft_gr_seam_closed") is False
        and result_review.get("qft_gr_seam_closure_authorized") is False
        and result_review.get("tranche_004_status_moved") is False
        and result_review.get("tranche_004_retained_blocker_discharged") is False,
        "no_release_theorem_phase_empirical_publication_or_master_promotion": result_review.get(
            "release_assembly_authorized"
        )
        is False
        and result_review.get("release_packet_assembled") is False
        and result_review.get("lean_theorem_debt_discharged") is False
        and result_review.get("proof_debt_reduced") is False
        and result_review.get("phase2_authorized") is False
        and result_review.get("empirical_validation_authorized") is False
        and result_review.get("publication_authorized") is False
        and result_review.get("master_action_promotion_authorized") is False,
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
        "attempt_id": ATTEMPT_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "executed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_FROM_RESEARCH_CANDIDATE_BLOCKED",
        "consumes_construction_packet_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_construction_packet_result_review_pointer": _ptr(result_review_path),
        "consumed_construction_packet_result_review_schema_id": result_review.get(
            "schema_id"
        ),
        "consumed_construction_packet_result_review_outcome_id": result_review.get(
            "outcome_id"
        ),
        "execution_scope": (
            "EXECUTE_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_FROM_"
            "RESEARCH_CANDIDATE_ONLY_NO_SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_OR_"
            "RELEASE_PROMOTION"
        ),
        "construction_target": CONSTRUCTION_TARGET,
        "construction_execution_target": EXECUTION_TARGET,
        "source_map_witness_chain_construction_executed": accepted,
        "source_map_witness_chain_construction_executed_from_research_candidate": accepted,
        "bounded_construction_execution_executed": accepted,
        "bounded_construction_execution_only": accepted,
        "construction_result_classification": CONSTRUCTION_RESULT_CLASSIFICATION,
        "result_classification_count": 1 if accepted else 0,
        "construction_result_classification_count": 1 if accepted else 0,
        "candidate_witness_chain_constructed_pending_result_review": accepted,
        "witness_chain_constructed_pending_result_review": accepted,
        "source_map_witness_chain_constructed_pending_result_review": accepted,
        "witness_chain_constructed": False,
        "source_map_witness_chain_constructed": False,
        "witness_chain_constructed_claimed": False,
        "source_map_witness_chain_constructed_claimed": False,
        "construction_result_claimed": False,
        "candidate_witness_chain_components": candidate_components,
        "candidate_witness_chain_component_count": len(candidate_components),
        "constructed_witness_chain_components": constructed_components,
        "constructed_witness_chain_component_count": len(constructed_components),
        "required_witness_chain_component_count": len(candidate_components),
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
        "construction_execution_steps": execution_steps,
        "construction_execution_step_count": len(execution_steps),
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": TRANCHE_004_FINDING_ID,
        "selected_dependency": TRANCHE_004_DEPENDENCY,
        "selected_dependency_class": "blocked_bridge_authorization_dependency",
        "accepted_input_classification": result_review.get("accepted_input_classification"),
        "construction_packet_result_review_classification": result_review.get(
            "result_review_classification"
        ),
        "construction_packet_result_review_accepted": result_review.get("accepted") is True,
        "bounded_construction_execution_authorized_by_review": result_review.get(
            "bounded_construction_execution_authorized_by_review"
        )
        is True,
        "source_map_witness_chain_construction_execution_authorized_by_review": result_review.get(
            "source_map_witness_chain_construction_execution_authorized_by_review"
        )
        is True,
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
        "retained_tranche_004_carry_forward": result_review.get(
            "retained_tranche_004_carry_forward", {}
        ),
        "required_future_route_for_tranche_004": TRANCHE_004_FUTURE_ROUTE,
        "release_readiness_decision_status": RELEASE_READINESS_DECISION,
        "release_readiness_held": True,
        "release_readiness_still_blocked": True,
        "release_readiness_proceed_authorized": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "readiness_marking_authorized": False,
        "v01_alpha_marked_ready": False,
        "source_map_closure_achieved": False,
        "source_map_closure_authorized": False,
        "source_map_closure_claimed": False,
        "qft_gr_source_map_semantic_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "qft_gr_seam_closure_authorized": False,
        "qft_gr_seam_closure_claimed": False,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "tranche_004_status_moved_by_execution": False,
        "tranche_004_status_moved": False,
        "tranche_004_retained_blocker_discharged": False,
        "blocker_movement_authorized": False,
        "blocker_movement_registered": False,
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
        else "REMEDIATE_V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_FROM_RESEARCH_CANDIDATE",
        "selected_next_target_kind": (
            "retained_tranche_004_source_map_witness_chain_construction_from_research_"
            "candidate_result_review_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_FROM_"
            "RESEARCH_CANDIDATE_RESULT_ONLY_NO_SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_OR_"
            "RELEASE_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained tranche 004 source-map witness-chain construction from "
            "research candidate executes only the bounded construction attempt "
            "authorized by the packet result review. It records the conservative "
            "classification witness_chain_constructed_pending_result_review and "
            "selects result review as the next target. It does not claim final "
            "witness-chain construction, source-map closure, QFT-GR seam closure, "
            "blocker movement, release assembly/readiness, theorem/proof-debt "
            "discharge, Phase 2, empirical validation, publication, master-action "
            "promotion, or external-truth status."
        ),
        "roadmap_update_required": True,
    }


def write_construction_execution(
    *,
    result_review_path: Path = DEFAULT_CONSTRUCTION_PACKET_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_construction_execution(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha retained tranche 004 source-map witness-chain "
            "construction execution from the accepted research candidate."
        )
    )
    parser.add_argument(
        "--result-review",
        type=Path,
        default=DEFAULT_CONSTRUCTION_PACKET_RESULT_REVIEW_PATH,
    )
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
    payload = write_construction_execution(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_source_map_witness_chain_construction_from_research_candidate_report: "
        f"accepted={payload['accepted']} classification={payload['construction_result_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
