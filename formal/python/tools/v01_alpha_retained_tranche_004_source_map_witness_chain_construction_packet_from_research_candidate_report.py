from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_result_review_report import (
    DEFAULT_OUT as DEFAULT_ATTEMPT_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_RESULT_REVIEW_SELECTED_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
)
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
from formal.python.tools.v01_alpha_retained_tranche_004_release_readiness_adjudication_report import (
    RELEASE_READINESS_DECISION,
    SELECTED_TRANCHE_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_"
    "FROM_RESEARCH_CANDIDATE_20260523_v0"
)
PACKET_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_"
    "FROM_RESEARCH_CANDIDATE_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_"
    "FROM_RESEARCH_CANDIDATE_PREPARED_WITH_NO_WITNESS_CONSTRUCTION_OR_SOURCE_MAP_CLOSURE"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_FROM_RESEARCH_CANDIDATE_20260523_v0.json"
)

NEXT_TARGET = (
    "review_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate_result"
)
CONSTRUCTION_EXECUTION_TARGET = (
    "execute_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_from_research_candidate"
)
REFINED_RESEARCH_TARGET = (
    "prepare_refined_v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt"
)
ASSEMBLE_RELEASE_PACKET_TARGET = "assemble_v01_alpha_release_packet"

MISSING_OBJECT = "source-map witness chain"
CONSTRUCTION_TARGET = (
    "construct_repo_local_source_map_witness_chain_for_retained_tranche_004_from_"
    "accepted_partial_research_candidate"
)

FORBIDDEN_EFFECTS = [
    "axiom_spec_backed_debt_reduced",
    "blocker_movement_authorized",
    "construction_execution_authorized_by_packet",
    "construction_packet_claimed_as_closure",
    "construction_packet_result_reviewed",
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
    "source_map_witness_chain_constructed",
    "source_map_witness_chain_construction_executed",
    "tranche_004_retained_blocker_discharged",
    "tranche_004_status_moved",
    "v01_alpha_marked_ready",
    "witness_chain_constructed",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _candidate_components(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    rows = list(result_review.get("candidate_witness_chain_component_checks", []))
    return [
        {
            "component_id": str(row.get("component_id")),
            "candidate_surface": row.get("surface"),
            "candidate_result_review_surface": row.get("result_review_surface"),
            "candidate_surface_exists": row.get("surface_exists") is True,
            "candidate_result_review_surface_exists": row.get("result_review_surface_exists")
            is True,
            "input_status": row.get("attempt_status"),
            "construction_packet_status": "candidate_input_only_not_constructed_by_packet",
        }
        for row in rows
    ]


def _required_proof_surfaces(candidate_components: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        {
            "surface_id": f"{component['component_id']}_construction_obligation",
            "candidate_surface": component["candidate_surface"],
            "candidate_result_review_surface": component["candidate_result_review_surface"],
            "required_future_use": (
                "future construction must either link this candidate component into a "
                "repo-local witness chain or record the exact fail-closed reason"
            ),
            "current_packet_status": "required_for_future_execution_not_constructed",
        }
        for component in candidate_components
    ]


def _required_evidence_surfaces() -> list[dict[str, str]]:
    return [
        {
            "evidence_id": "accepted_partial_candidate_input",
            "required_evidence": "The accepted result-review packet and its exact conservative classification.",
            "current_packet_status": "input_consumed_only",
        },
        {
            "evidence_id": "component_status_matrix",
            "required_evidence": "A per-component proved/supplied/missing/refuted status matrix.",
            "current_packet_status": "required_for_future_execution",
        },
        {
            "evidence_id": "semantic_transport_link_map",
            "required_evidence": "A link map from quantum expectation semantics to classical source admissibility.",
            "current_packet_status": "required_for_future_execution",
        },
        {
            "evidence_id": "conservation_and_bianchi_compatibility_trace",
            "required_evidence": "A trace showing conservation and Bianchi compatibility obligations are not bypassed.",
            "current_packet_status": "required_for_future_execution",
        },
        {
            "evidence_id": "einstein_coupling_and_weak_curvature_trace",
            "required_evidence": "A trace separating local coupling/source-identification candidates from closure claims.",
            "current_packet_status": "required_for_future_execution",
        },
        {
            "evidence_id": "result_review_and_status_movement_control",
            "required_evidence": "A future review/control surface before execution, closure, or blocker movement can be considered.",
            "current_packet_status": "required_for_future_review",
        },
    ]


def _success_criteria() -> list[dict[str, str]]:
    return [
        {
            "criterion_id": "all_candidate_components_accounted_for",
            "criterion": "Every accepted candidate component is linked, refuted, or retained with an exact reason.",
            "required_future_stage": "construction_execution_and_result_review",
        },
        {
            "criterion_id": "semantic_transport_chain_explicit",
            "criterion": "The route explicitly connects expectation semantics, source admissibility, conservation, and coupling obligations.",
            "required_future_stage": "construction_execution_and_result_review",
        },
        {
            "criterion_id": "closure_requires_separate_valid_chain",
            "criterion": "Source-map closure remains unavailable unless a separately valid witness chain is constructed and reviewed.",
            "required_future_stage": "post_construction_result_review",
        },
        {
            "criterion_id": "release_hold_survives_packet",
            "criterion": "Release readiness remains held and assembly remains unauthorized throughout packet preparation.",
            "required_future_stage": "any_future_release_adjudication",
        },
    ]


def _failure_criteria() -> list[dict[str, str]]:
    return [
        {
            "criterion_id": "candidate_component_unlinked",
            "condition": "A candidate component cannot be linked into the source-map witness-chain route.",
            "required_result": "fail_closed_retained_blocker_or_refined_research",
        },
        {
            "criterion_id": "candidate_component_supplied_only",
            "condition": "A component remains supplied-only without adequate repo-local construction support.",
            "required_result": "source_map_closure_not_authorized",
        },
        {
            "criterion_id": "semantic_transport_gap_persists",
            "condition": "The route cannot preserve meaning from QFT expectation objects to a classical GR source.",
            "required_result": "qft_gr_seam_remains_open",
        },
        {
            "criterion_id": "closure_inferred_from_packet",
            "condition": "Packet preparation is treated as witness-chain construction or closure evidence.",
            "required_result": "reject_route_no_status_movement",
        },
        {
            "criterion_id": "release_or_blocker_movement_requested",
            "condition": "Release assembly, readiness marking, or tranche 004 movement is requested before construction result review.",
            "required_result": "release_hold_continues",
        },
    ]


def _construction_execution_boundary() -> list[dict[str, str]]:
    return [
        {
            "boundary_id": "packet_preparation_only",
            "rule": "This packet prepares construction scope; it does not execute construction.",
        },
        {
            "boundary_id": "review_before_execution",
            "rule": "The prepared packet must be reviewed before construction execution can be authorized.",
        },
        {
            "boundary_id": "no_status_movement_by_preparation",
            "rule": "Tranche 004 remains retained release-blocking by preparation alone.",
        },
        {
            "boundary_id": "closure_requires_future_witness_chain",
            "rule": "No source-map or QFT-GR seam closure follows from this packet.",
        },
        {
            "boundary_id": "release_lane_stays_held",
            "rule": "Release readiness remains held and release assembly remains unauthorized.",
        },
    ]


def build_construction_packet(
    *,
    result_review_path: Path = DEFAULT_ATTEMPT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    candidate_components = _candidate_components(result_review)
    required_proof_surfaces = _required_proof_surfaces(candidate_components)
    required_evidence_surfaces = _required_evidence_surfaces()
    success_criteria = _success_criteria()
    failure_criteria = _failure_criteria()
    construction_boundary = _construction_execution_boundary()
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    candidate_next_targets = [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The prepared construction packet must be reviewed before any "
                "construction execution target can be authorized."
            ),
        },
        {
            "target": CONSTRUCTION_EXECUTION_TARGET,
            "decision": "deferred",
            "reason": "Construction execution is not authorized by packet preparation.",
        },
        {
            "target": REFINED_RESEARCH_TARGET,
            "decision": "deferred",
            "reason": "Refined research remains available if the prepared packet is rejected.",
        },
        {
            "target": ASSEMBLE_RELEASE_PACKET_TARGET,
            "decision": "not_authorized",
            "reason": "Release assembly remains blocked by retained tranche 004.",
        },
    ]

    retained_tranche_004 = dict(result_review.get("retained_tranche_004_carry_forward", {}))
    candidate_statuses = {row.get("construction_packet_status") for row in candidate_components}

    acceptance_criteria = {
        "consumes_expected_attempt_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_schema_expected": result_review.get("schema_id")
        == EXPECTED_RESULT_REVIEW_SCHEMA_ID,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_selected_this_packet": result_review.get("selected_next_target")
        == EXPECTED_RESULT_REVIEW_SELECTED_TARGET,
        "result_review_accepted_partial_candidate_only": result_review.get("accepted") is True
        and result_review.get("result_review_classification")
        == RESULT_REVIEW_CLASSIFICATION
        and result_review.get(
            "partial_witness_chain_candidate_accepted_for_construction_packet_preparation_only"
        )
        is True,
        "result_review_authorized_preparation_only": result_review.get(
            "construction_packet_preparation_authorized"
        )
        is True
        and result_review.get("construction_packet_preparation_only") is True
        and result_review.get("source_map_witness_chain_construction_packet_prepared")
        is False,
        "candidate_component_count_expected": len(candidate_components) == 7
        and result_review.get("candidate_witness_chain_component_check_count") == 7
        and result_review.get("candidate_witness_chain_surface_found_count") == 7,
        "candidate_components_are_inputs_only": candidate_statuses
        == {"candidate_input_only_not_constructed_by_packet"}
        and all(row["candidate_surface_exists"] for row in candidate_components)
        and all(row["candidate_result_review_surface_exists"] for row in candidate_components),
        "tranche_004_retained": result_review.get("tranche_004_status")
        == TRANCHE_004_STATUS
        and retained_tranche_004.get("status") == TRANCHE_004_STATUS
        and retained_tranche_004.get("dependency_finding_id") == TRANCHE_004_FINDING_ID
        and retained_tranche_004.get("dependency") == TRANCHE_004_DEPENDENCY
        and retained_tranche_004.get("current_blocker") == TRANCHE_004_CURRENT_BLOCKER
        and retained_tranche_004.get("retained_blocker_reason")
        == TRANCHE_004_RETAINED_REASON,
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
        and result_review.get("tranche_006_dependency_finding_id") == TRANCHE_006_FINDING_ID
        and result_review.get("documented_dependency_nonblocking_tranche_count") == 5,
        "release_hold_preserved": result_review.get("release_readiness_decision_status")
        == RELEASE_READINESS_DECISION
        and result_review.get("release_readiness_held") is True
        and result_review.get("release_readiness_still_blocked") is True
        and result_review.get("release_readiness_proceed_authorized") is False,
        "no_construction_closure_or_blocker_movement_in_input": result_review.get(
            "witness_chain_constructed"
        )
        is False
        and result_review.get("source_map_witness_chain_constructed") is False
        and result_review.get("source_map_witness_chain_construction_executed") is False
        and result_review.get("source_map_closure_claimed") is False
        and result_review.get("qft_gr_seam_closed") is False
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
        "packet_sections_defined": len(required_proof_surfaces) == 7
        and len(required_evidence_surfaces) == 6
        and len(success_criteria) == 4
        and len(failure_criteria) == 5
        and len(construction_boundary) == 5,
        "selected_next_target_is_review_only": NEXT_TARGET
        != CONSTRUCTION_EXECUTION_TARGET
        and candidate_next_targets[0]["target"] == NEXT_TARGET,
        "forbidden_effects_all_false": all(
            value is False for value in forbidden_effect_status.values()
        ),
        "exactly_one_next_target_selected": sum(
            1 for row in candidate_next_targets if row["decision"] == "selected"
        )
        == 1,
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
        else "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_FROM_RESEARCH_CANDIDATE_BLOCKED",
        "consumes_research_attempt_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_research_attempt_result_review_pointer": _ptr(result_review_path),
        "consumed_research_attempt_result_review_schema_id": result_review.get("schema_id"),
        "consumed_research_attempt_result_review_outcome_id": result_review.get("outcome_id"),
        "packet_scope": (
            "PREPARE_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_"
            "FROM_RESEARCH_CANDIDATE_ONLY_NO_WITNESS_CONSTRUCTION_SOURCE_MAP_CLOSURE_"
            "BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "construction_packet_prepared": accepted,
        "construction_packet_prepared_only": accepted,
        "source_map_witness_chain_construction_packet_prepared": accepted,
        "source_map_witness_chain_construction_packet_prepared_from_research_candidate": accepted,
        "construction_target": CONSTRUCTION_TARGET,
        "construction_execution_target": CONSTRUCTION_EXECUTION_TARGET,
        "construction_execution_authorized_by_packet": False,
        "source_map_witness_chain_construction_executed": False,
        "witness_chain_constructed": False,
        "source_map_witness_chain_constructed": False,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": TRANCHE_004_FINDING_ID,
        "selected_dependency": TRANCHE_004_DEPENDENCY,
        "selected_dependency_class": "blocked_bridge_authorization_dependency",
        "blocked_object": BLOCKED_OBJECT,
        "missing_object": MISSING_OBJECT,
        "accepted_input_classification": RESULT_REVIEW_CLASSIFICATION,
        "partial_witness_chain_candidate_accepted_for_construction_packet_preparation_only": accepted,
        "candidate_witness_chain_components": candidate_components,
        "candidate_witness_chain_component_count": len(candidate_components),
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
        "retained_tranche_004_carry_forward": retained_tranche_004,
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
        "construction_packet_claimed_as_closure": False,
        "qft_gr_source_map_semantic_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "qft_gr_seam_closure_authorized": False,
        "qft_gr_seam_closure_claimed": False,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "tranche_004_status_moved_by_packet": False,
        "tranche_004_status_moved": False,
        "tranche_004_retained_blocker_discharged": False,
        "blocker_movement_authorized": False,
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
        "post_packet_review_target": NEXT_TARGET,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_FROM_RESEARCH_CANDIDATE",
        "selected_next_target_kind": (
            "source_map_witness_chain_construction_packet_from_research_candidate_"
            "result_review_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_"
            "FROM_RESEARCH_CANDIDATE_ONLY_NO_CONSTRUCTION_EXECUTION_SOURCE_MAP_CLOSURE_"
            "BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained tranche 004 source-map witness-chain construction packet "
            "from research candidate prepares a future construction route only. It "
            "does not execute construction, construct a witness chain, claim source-map "
            "closure, close the QFT-GR seam, move tranche 004, assemble release, mark "
            "readiness, discharge theorem/proof debt or retained assumptions, authorize "
            "Phase 2, authorize empirical validation, authorize publication, promote "
            "the master action, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_construction_packet(
    *,
    result_review_path: Path = DEFAULT_ATTEMPT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_construction_packet(
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
            "construction packet from the accepted research candidate."
        )
    )
    parser.add_argument(
        "--result-review",
        type=Path,
        default=DEFAULT_ATTEMPT_RESULT_REVIEW_PATH,
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
    payload = write_construction_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
