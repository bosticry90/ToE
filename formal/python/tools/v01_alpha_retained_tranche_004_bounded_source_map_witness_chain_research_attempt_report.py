from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_packet_report import (
    BLOCKED_OBJECT,
    RESEARCH_PACKET_MISSING_OBJECT,
)
from formal.python.tools.v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_packet_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_PACKET_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_REVIEW_SELECTED_TARGET,
    OUTCOME_ID as EXPECTED_REVIEW_OUTCOME,
    REVIEW_ID as EXPECTED_REVIEW_ID,
    SCHEMA_ID as EXPECTED_REVIEW_SCHEMA_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
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


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_"
    "20260523_v0"
)
ATTEMPT_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_"
    "EXECUTED_WITH_NO_SOURCE_MAP_CLOSURE_OR_RELEASE_PROMOTION"
)
RESEARCH_ATTEMPT_CLASSIFICATION = "partial_witness_chain_candidate_pending_review"
NEXT_TARGET = (
    "review_v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_result"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_20260523_v0.json"
)

FORBIDDEN_EFFECTS = [
    "source_map_closure_claimed",
    "qft_gr_source_map_semantic_closure_claimed",
    "qft_gr_seam_closed",
    "qft_gr_seam_closure_claimed",
    "witness_chain_constructed",
    "source_map_witness_chain_constructed",
    "tranche_004_status_moved",
    "tranche_004_retained_blocker_discharged",
    "release_assembly_authorized",
    "release_packet_assembled",
    "readiness_marking_authorized",
    "v01_alpha_marked_ready",
    "lean_theorem_debt_discharged",
    "axiom_spec_backed_debt_reduced",
    "proof_debt_reduced",
    "retained_assumptions_discharged",
    "phase2_authorized",
    "empirical_validation_authorized",
    "master_action_promotion_authorized",
]

RESEARCH_SURFACES = [
    {
        "component_id": "state_expectation_functional_semantics",
        "surface": "formal/toe_formal/ToeFormal/Bridges/QFT_GR_StateExpectationFunctionalSemantics.lean",
        "result_review_surface": "formal/toe_formal/ToeFormal/Bridges/QFT_GR_StateExpectationFunctionalSemanticsResultReview.lean",
        "attempt_status": "repo_local_candidate_surface_found_supplied_only_not_closure",
    },
    {
        "component_id": "renormalized_expectation_value_semantics",
        "surface": "formal/toe_formal/ToeFormal/Bridges/QFT_GR_RenormalizedExpectationValueSemantics.lean",
        "result_review_surface": "formal/toe_formal/ToeFormal/Bridges/QFT_GR_RenormalizedExpectationValueSemanticsResultReview.lean",
        "attempt_status": "repo_local_candidate_surface_found_supplied_only_not_closure",
    },
    {
        "component_id": "classical_source_admissibility_semantics",
        "surface": "formal/toe_formal/ToeFormal/Bridges/QFT_GR_ClassicalSourceAdmissibilitySemantics.lean",
        "result_review_surface": "formal/toe_formal/ToeFormal/Bridges/QFT_GR_ClassicalSourceAdmissibilitySemanticsResultReview.lean",
        "attempt_status": "repo_local_candidate_surface_found_supplied_only_not_closure",
    },
    {
        "component_id": "covariant_conservation_obligation",
        "surface": "formal/toe_formal/ToeFormal/Bridges/QFT_GR_CovariantConservationObligationSemantics.lean",
        "result_review_surface": "formal/toe_formal/ToeFormal/Bridges/QFT_GR_CovariantConservationObligationSemanticsResultReview.lean",
        "attempt_status": "repo_local_candidate_surface_found_supplied_only_not_closure",
    },
    {
        "component_id": "bianchi_compatibility_obligation",
        "surface": "formal/toe_formal/ToeFormal/Bridges/QFT_GR_BianchiCompatibilityObligationSemantics.lean",
        "result_review_surface": "formal/toe_formal/ToeFormal/Bridges/QFT_GR_BianchiCompatibilityObligationSemanticsResultReview.lean",
        "attempt_status": "repo_local_candidate_surface_found_supplied_only_not_closure",
    },
    {
        "component_id": "einstein_coupling_obligation",
        "surface": "formal/toe_formal/ToeFormal/Bridges/QFT_GR_EinsteinCouplingObligationSemantics.lean",
        "result_review_surface": "formal/toe_formal/ToeFormal/Bridges/QFT_GR_EinsteinCouplingObligationSemanticsResultReview.lean",
        "attempt_status": "repo_local_candidate_surface_found_supplied_only_not_closure",
    },
    {
        "component_id": "weak_curvature_source_identification",
        "surface": "formal/toe_formal/ToeFormal/Bridges/QFT_GR_WeakCurvatureSourceIdentificationObligationSemantics.lean",
        "result_review_surface": "formal/toe_formal/ToeFormal/Bridges/QFT_GR_WeakCurvatureSourceIdentificationObligationSemanticsResultReview.lean",
        "attempt_status": "repo_local_candidate_surface_found_supplied_only_not_closure",
    },
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _path_exists(pointer: str) -> bool:
    return (REPO_ROOT / pointer).exists()


def build_attempt(
    *,
    packet_result_review_path: Path = DEFAULT_PACKET_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(packet_result_review_path)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}
    surface_checks = [
        {
            **row,
            "surface_exists": _path_exists(row["surface"]),
            "result_review_surface_exists": _path_exists(row["result_review_surface"]),
        }
        for row in RESEARCH_SURFACES
    ]
    found_count = sum(
        1
        for row in surface_checks
        if row["surface_exists"] and row["result_review_surface_exists"]
    )
    candidate_next_targets = [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": "The bounded research attempt result requires governed review before any construction packet or refinement.",
        },
        {
            "target": "prepare_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate",
            "decision": "deferred",
            "reason": "A construction packet can only be considered after result review accepts the partial candidate.",
        },
        {
            "target": "prepare_refined_v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt",
            "decision": "deferred",
            "reason": "Refinement remains available if result review rejects or narrows the candidate.",
        },
        {
            "target": "assemble_v01_alpha_release_packet",
            "decision": "not_authorized",
            "reason": "Release assembly remains blocked by retained tranche 004.",
        },
    ]

    acceptance_criteria = {
        "consumes_expected_packet_result_review": review.get("review_id")
        == EXPECTED_REVIEW_ID,
        "packet_result_review_schema_expected": review.get("schema_id")
        == EXPECTED_REVIEW_SCHEMA_ID,
        "packet_result_review_accepted": review.get("accepted") is True
        and review.get("outcome_id") == EXPECTED_REVIEW_OUTCOME,
        "packet_result_review_selected_this_attempt": review.get("selected_next_target")
        == EXPECTED_REVIEW_SELECTED_TARGET,
        "attempt_authorized_by_review": review.get(
            "bounded_source_map_witness_chain_research_attempt_authorized_for_execution"
        )
        is True,
        "research_surfaces_checked": len(surface_checks) == 7 and found_count == 7,
        "classification_is_single_allowed_result": RESEARCH_ATTEMPT_CLASSIFICATION
        == "partial_witness_chain_candidate_pending_review",
        "tranche_004_retained": review.get("tranche_004_status") == TRANCHE_004_STATUS,
        "release_hold_preserved": review.get("release_readiness_decision_status")
        == RELEASE_READINESS_DECISION,
        "no_closure_or_status_movement": all(
            forbidden_effect_status[key] is False for key in FORBIDDEN_EFFECTS
        ),
        "exactly_one_next_target_selected": sum(
            1 for row in candidate_next_targets if row["decision"] == "selected"
        )
        == 1,
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "attempt_id": ATTEMPT_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_BLOCKED",
        "consumes_bounded_source_map_witness_chain_research_packet_result_review": EXPECTED_REVIEW_ID,
        "consumes_bounded_source_map_witness_chain_research_packet_result_review_pointer": _ptr(
            packet_result_review_path
        ),
        "consumed_bounded_source_map_witness_chain_research_packet_result_review_schema_id": review.get(
            "schema_id"
        ),
        "attempt_scope": (
            "EXECUTE_BOUNDED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_ONLY_"
            "NO_SOURCE_MAP_CLOSURE_RELEASE_ASSEMBLY_STATUS_MOVEMENT_OR_PROMOTION"
        ),
        "research_attempt_executed": accepted,
        "bounded_source_map_witness_chain_research_attempt_executed": accepted,
        "research_attempt_result_classification": RESEARCH_ATTEMPT_CLASSIFICATION,
        "result_classification_count": 1,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": TRANCHE_004_FINDING_ID,
        "selected_dependency": TRANCHE_004_DEPENDENCY,
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
        "documented_dependency_nonblocking_tranche_count": 5,
        "retained_tranche_004_carry_forward": review.get(
            "retained_tranche_004_carry_forward"
        ),
        "required_future_route_for_tranche_004": TRANCHE_004_FUTURE_ROUTE,
        "release_readiness_decision_status": RELEASE_READINESS_DECISION,
        "release_readiness_held": True,
        "release_readiness_still_blocked": True,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "candidate_witness_chain_component_checks": surface_checks,
        "candidate_witness_chain_component_check_count": len(surface_checks),
        "candidate_witness_chain_surface_found_count": found_count,
        "partial_witness_chain_candidate_produced": True,
        "partial_witness_chain_candidate_pending_review": True,
        "witness_chain_constructed": False,
        "source_map_witness_chain_constructed": False,
        "source_map_closure_claimed": False,
        "qft_gr_source_map_semantic_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "qft_gr_seam_closure_claimed": False,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "tranche_004_status_moved_by_attempt": False,
        "tranche_004_retained_blocker_discharged": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "phase2_authorized": False,
        "empirical_validation_authorized": False,
        "master_action_promotion_authorized": False,
        "forbidden_effect_status": forbidden_effect_status,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT",
        "selected_next_target_kind": "bounded_source_map_witness_chain_research_attempt_result_review_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_RESULT_ONLY_"
            "NO_SOURCE_MAP_CLOSURE_RELEASE_ASSEMBLY_STATUS_MOVEMENT_OR_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained tranche 004 bounded source-map witness-chain research attempt "
            "executes the authorized research slice and records a partial witness-chain "
            "candidate pending result review. It does not construct a governed witness "
            "chain, claim source-map closure, close the QFT-GR seam, move tranche 004, "
            "assemble release, mark readiness, discharge theorem/proof debt or retained "
            "assumptions, authorize Phase 2 or empirical validation, promote the master "
            "action, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_attempt(
    *,
    packet_result_review_path: Path = DEFAULT_PACKET_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_attempt(
        packet_result_review_path=packet_result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha retained tranche 004 bounded source-map "
            "witness-chain research attempt."
        )
    )
    parser.add_argument("--packet-result-review", type=Path, default=DEFAULT_PACKET_RESULT_REVIEW_PATH)
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
    payload = write_attempt(
        packet_result_review_path=packet_result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_report: "
        f"accepted={payload['accepted']} classification={payload['research_attempt_result_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
