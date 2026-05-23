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
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate_report import (
    ASSEMBLE_RELEASE_PACKET_TARGET,
    CONSTRUCTION_EXECUTION_TARGET,
    DEFAULT_OUT as DEFAULT_CONSTRUCTION_PACKET_PATH,
    OUTCOME_ID as EXPECTED_CONSTRUCTION_PACKET_OUTCOME,
    PACKET_ID as EXPECTED_CONSTRUCTION_PACKET_ID,
    REFINED_RESEARCH_TARGET,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_ACCEPTED_INPUT_CLASSIFICATION,
    SCHEMA_ID as EXPECTED_CONSTRUCTION_PACKET_SCHEMA_ID,
    MISSING_OBJECT,
    NEXT_TARGET as EXPECTED_PACKET_SELECTED_TARGET,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_"
    "FROM_RESEARCH_CANDIDATE_RESULT_REVIEW_20260523_v0"
)
REVIEW_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_"
    "FROM_RESEARCH_CANDIDATE_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_"
    "FROM_RESEARCH_CANDIDATE_RESULT_REVIEW_ACCEPTS_CONSTRUCTION_PACKET_AND_AUTHORIZES_"
    "BOUNDED_CONSTRUCTION_EXECUTION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "construction_packet_accepted_bounded_construction_execution_authorized_only"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_FROM_RESEARCH_CANDIDATE_RESULT_REVIEW_20260523_v0.json"
)

NEXT_TARGET = CONSTRUCTION_EXECUTION_TARGET
POST_CONSTRUCTION_RESULT_REVIEW_TARGET = (
    "review_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_from_research_candidate_result"
)

FORBIDDEN_EFFECTS = [
    "axiom_spec_backed_debt_reduced",
    "blocker_movement_authorized",
    "blocker_movement_registered",
    "construction_packet_claimed_as_closure",
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
    "source_map_witness_chain_constructed",
    "source_map_witness_chain_construction_executed",
    "tranche_004_retained_blocker_discharged",
    "tranche_004_status_moved",
    "unbounded_construction_execution_authorized",
    "v01_alpha_marked_ready",
    "witness_chain_constructed",
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
                "The construction packet is accepted for bounded execution only; "
                "execution still must record an exact conservative result classification."
            ),
        },
        {
            "target": POST_CONSTRUCTION_RESULT_REVIEW_TARGET,
            "decision": "deferred",
            "reason": "A construction result review is available only after execution records a result.",
        },
        {
            "target": REFINED_RESEARCH_TARGET,
            "decision": "deferred",
            "reason": "Refined research remains available if bounded construction cannot proceed.",
        },
        {
            "target": ASSEMBLE_RELEASE_PACKET_TARGET,
            "decision": "not_authorized",
            "reason": "Release assembly remains blocked by retained tranche 004.",
        },
    ]


def build_construction_packet_result_review(
    *,
    construction_packet_path: Path = DEFAULT_CONSTRUCTION_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(construction_packet_path)
    candidate_components = list(packet.get("candidate_witness_chain_components", []))
    required_proof_surfaces = list(packet.get("required_proof_surfaces", []))
    required_evidence_surfaces = list(packet.get("required_evidence_surfaces", []))
    success_criteria = list(packet.get("success_criteria", []))
    failure_criteria = list(packet.get("failure_criteria", []))
    construction_boundary = list(packet.get("construction_execution_boundary", []))
    candidate_next_targets = _candidate_next_targets()
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_construction_packet": packet.get("packet_id")
        == EXPECTED_CONSTRUCTION_PACKET_ID,
        "construction_packet_schema_expected": packet.get("schema_id")
        == EXPECTED_CONSTRUCTION_PACKET_SCHEMA_ID,
        "construction_packet_outcome_expected": packet.get("outcome_id")
        == EXPECTED_CONSTRUCTION_PACKET_OUTCOME,
        "construction_packet_selected_this_review": packet.get("selected_next_target")
        == EXPECTED_PACKET_SELECTED_TARGET,
        "construction_packet_prepared_only": packet.get("accepted") is True
        and packet.get("prepared") is True
        and packet.get("construction_packet_prepared") is True
        and packet.get("construction_packet_prepared_only") is True
        and packet.get("source_map_witness_chain_construction_packet_prepared") is True
        and packet.get(
            "source_map_witness_chain_construction_packet_prepared_from_research_candidate"
        )
        is True,
        "input_classification_remains_partial_candidate_only": packet.get(
            "accepted_input_classification"
        )
        == EXPECTED_ACCEPTED_INPUT_CLASSIFICATION
        and packet.get(
            "partial_witness_chain_candidate_accepted_for_construction_packet_preparation_only"
        )
        is True,
        "packet_did_not_authorize_execution": packet.get(
            "construction_execution_authorized_by_packet"
        )
        is False,
        "candidate_material_carried": len(candidate_components) == 7
        and packet.get("candidate_witness_chain_component_count") == 7
        and len(required_proof_surfaces) == 7
        and packet.get("required_proof_surface_count") == 7
        and len(required_evidence_surfaces) == 6
        and packet.get("required_evidence_surface_count") == 6,
        "criteria_and_boundaries_carried": len(success_criteria) == 4
        and packet.get("success_criteria_count") == 4
        and len(failure_criteria) == 5
        and packet.get("failure_criteria_count") == 5
        and len(construction_boundary) == 5
        and packet.get("construction_execution_boundary_count") == 5,
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
        "construction_not_yet_executed": packet.get(
            "source_map_witness_chain_construction_executed"
        )
        is False
        and packet.get("witness_chain_constructed") is False
        and packet.get("source_map_witness_chain_constructed") is False,
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
        "bounded_execution_selected_only": sum(
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
        else "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_FROM_RESEARCH_CANDIDATE_RESULT_REVIEW_BLOCKED",
        "consumes_construction_packet_from_research_candidate": (
            EXPECTED_CONSTRUCTION_PACKET_ID
        ),
        "consumes_construction_packet_from_research_candidate_pointer": _ptr(
            construction_packet_path
        ),
        "consumed_construction_packet_schema_id": packet.get("schema_id"),
        "consumed_construction_packet_outcome_id": packet.get("outcome_id"),
        "review_scope": (
            "REVIEW_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_"
            "FROM_RESEARCH_CANDIDATE_RESULT_ONLY_NO_CONSTRUCTION_EXECUTION_SOURCE_MAP_"
            "CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "construction_packet_result_reviewed": accepted,
        "construction_packet_result_accepted": accepted,
        "construction_packet_accepted_for_bounded_construction_execution_only": accepted,
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "result_classification_count": 1 if accepted else 0,
        "accepted_input_classification": packet.get("accepted_input_classification"),
        "construction_packet_prepared": packet.get("construction_packet_prepared") is True,
        "construction_packet_prepared_only": packet.get("construction_packet_prepared_only")
        is True,
        "source_map_witness_chain_construction_packet_prepared": packet.get(
            "source_map_witness_chain_construction_packet_prepared"
        )
        is True,
        "source_map_witness_chain_construction_packet_prepared_from_research_candidate": packet.get(
            "source_map_witness_chain_construction_packet_prepared_from_research_candidate"
        )
        is True,
        "construction_execution_authorized_by_packet": False,
        "bounded_construction_execution_authorized": accepted,
        "bounded_construction_execution_authorized_by_review": accepted,
        "source_map_witness_chain_construction_execution_authorized": accepted,
        "source_map_witness_chain_construction_execution_authorized_by_review": accepted,
        "construction_execution_target": NEXT_TARGET,
        "post_construction_result_review_target": POST_CONSTRUCTION_RESULT_REVIEW_TARGET,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": TRANCHE_004_FINDING_ID,
        "selected_dependency": TRANCHE_004_DEPENDENCY,
        "selected_dependency_class": "blocked_bridge_authorization_dependency",
        "blocked_object": packet.get("blocked_object"),
        "missing_object": MISSING_OBJECT,
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
        "retained_tranche_004_carry_forward": packet.get(
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
        "source_map_witness_chain_construction_executed": False,
        "witness_chain_constructed": False,
        "source_map_witness_chain_constructed": False,
        "source_map_closure_achieved": False,
        "source_map_closure_authorized": False,
        "source_map_closure_claimed": False,
        "construction_packet_claimed_as_closure": False,
        "qft_gr_source_map_semantic_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "qft_gr_seam_closure_authorized": False,
        "qft_gr_seam_closure_claimed": False,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "tranche_004_status_moved_by_review": False,
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
        else "REMEDIATE_V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_FROM_RESEARCH_CANDIDATE_RESULT_REVIEW",
        "selected_next_target_kind": (
            "bounded_source_map_witness_chain_construction_from_research_candidate_"
            "execution_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "EXECUTE_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_FROM_"
            "RESEARCH_CANDIDATE_ONLY_NO_SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_OR_"
            "RELEASE_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained tranche 004 construction-packet result review accepts the "
            "prepared packet and authorizes only bounded construction execution as "
            "the next target. It does not execute construction, construct a witness "
            "chain, claim source-map closure, close the QFT-GR seam, move tranche 004, "
            "assemble release, mark readiness, discharge theorem/proof debt or retained "
            "assumptions, authorize Phase 2, authorize empirical validation, authorize "
            "publication, promote the master action, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_construction_packet_result_review(
    *,
    construction_packet_path: Path = DEFAULT_CONSTRUCTION_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_construction_packet_result_review(
        construction_packet_path=construction_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha retained tranche 004 source-map witness-chain "
            "construction packet from research candidate result review."
        )
    )
    parser.add_argument(
        "--construction-packet",
        type=Path,
        default=DEFAULT_CONSTRUCTION_PACKET_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    construction_packet_path = (
        ns.construction_packet
        if ns.construction_packet.is_absolute()
        else (REPO_ROOT / ns.construction_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_construction_packet_result_review(
        construction_packet_path=construction_packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate_result_review_report: "
        f"accepted={payload['accepted']} classification={payload['result_review_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
