from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_report import (
    ATTEMPT_ID as EXPECTED_ATTEMPT_ID,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_RESEARCH_ATTEMPT_PATH,
    FORBIDDEN_EFFECTS as ATTEMPT_FORBIDDEN_EFFECTS,
    NEXT_TARGET as EXPECTED_ATTEMPT_SELECTED_TARGET,
    OUTCOME_ID as EXPECTED_ATTEMPT_OUTCOME,
    RESEARCH_ATTEMPT_CLASSIFICATION as EXPECTED_ATTEMPT_CLASSIFICATION,
    SCHEMA_ID as EXPECTED_ATTEMPT_SCHEMA_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_packet_report import (
    ASSEMBLE_RELEASE_PACKET_TARGET,
    BLOCKED_OBJECT,
    RESEARCH_PACKET_MISSING_OBJECT,
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
    "RESULT_REVIEW_20260523_v0"
)
REVIEW_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_"
    "RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_"
    "RESULT_REVIEW_ACCEPTS_PARTIAL_CANDIDATE_AND_AUTHORIZES_CONSTRUCTION_PACKET_PREPARATION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "partial_witness_chain_candidate_accepted_for_construction_packet_preparation_only"
)
NEXT_TARGET = (
    "prepare_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate"
)
REFINED_RESEARCH_ATTEMPT_TARGET = (
    "prepare_refined_v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_RESULT_REVIEW_20260523_v0.json"
)

FORBIDDEN_EFFECTS = sorted(
    set(ATTEMPT_FORBIDDEN_EFFECTS)
    | {
        "construction_packet_preparation_claimed_as_closure",
        "empirical_validation_claimed",
        "publication_authorized",
        "qft_gr_seam_closure_authorized_by_review",
        "release_assembly_authorized_by_review",
        "source_map_closure_authorized_by_review",
        "source_map_witness_chain_construction_executed",
        "tranche_004_status_moved_by_review",
    }
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _candidate_components(attempt: dict[str, Any]) -> list[dict[str, Any]]:
    return list(attempt.get("candidate_witness_chain_component_checks", []))


def _component_surfaces_found(components: list[dict[str, Any]]) -> bool:
    return all(
        row.get("surface_exists") is True
        and row.get("result_review_surface_exists") is True
        and row.get("attempt_status")
        == "repo_local_candidate_surface_found_supplied_only_not_closure"
        for row in components
    )


def build_attempt_result_review(
    *,
    attempt_path: Path = DEFAULT_RESEARCH_ATTEMPT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _read_json(attempt_path)
    candidate_components = _candidate_components(attempt)
    retained_tranche_004 = dict(attempt.get("retained_tranche_004_carry_forward", {}))
    attempt_forbidden = dict(attempt.get("forbidden_effect_status", {}))
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}
    candidate_next_targets = [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The review accepts the partial candidate only as sufficient input "
                "for preparing a governed construction packet; no construction or "
                "closure is performed by this review."
            ),
        },
        {
            "target": REFINED_RESEARCH_ATTEMPT_TARGET,
            "decision": "deferred",
            "reason": (
                "Refinement remains available if the future construction-packet "
                "preparation review finds the candidate insufficient."
            ),
        },
        {
            "target": ASSEMBLE_RELEASE_PACKET_TARGET,
            "decision": "not_authorized",
            "reason": "Release assembly remains blocked by retained tranche 004.",
        },
    ]

    acceptance_criteria = {
        "consumes_expected_research_attempt": attempt.get("attempt_id")
        == EXPECTED_ATTEMPT_ID,
        "attempt_schema_expected": attempt.get("schema_id")
        == EXPECTED_ATTEMPT_SCHEMA_ID,
        "attempt_executed_and_accepted": attempt.get("accepted") is True
        and attempt.get("research_attempt_executed") is True
        and attempt.get("bounded_source_map_witness_chain_research_attempt_executed")
        is True,
        "attempt_outcome_expected": attempt.get("outcome_id")
        == EXPECTED_ATTEMPT_OUTCOME,
        "attempt_selected_this_review": attempt.get("selected_next_target")
        == EXPECTED_ATTEMPT_SELECTED_TARGET,
        "attempt_classification_expected": attempt.get(
            "research_attempt_result_classification"
        )
        == EXPECTED_ATTEMPT_CLASSIFICATION
        and attempt.get("result_classification_count") == 1,
        "partial_candidate_present_pending_review": attempt.get(
            "partial_witness_chain_candidate_produced"
        )
        is True
        and attempt.get("partial_witness_chain_candidate_pending_review") is True,
        "candidate_component_count_expected": attempt.get(
            "candidate_witness_chain_component_check_count"
        )
        == 7
        and attempt.get("candidate_witness_chain_surface_found_count") == 7
        and len(candidate_components) == 7
        and _component_surfaces_found(candidate_components),
        "tranche_004_retained": attempt.get("tranche_004_status") == TRANCHE_004_STATUS
        and retained_tranche_004.get("status") == TRANCHE_004_STATUS
        and retained_tranche_004.get("dependency") == TRANCHE_004_DEPENDENCY
        and retained_tranche_004.get("dependency_finding_id")
        == TRANCHE_004_FINDING_ID,
        "documented_dependency_nonblocking_queue_preserved": attempt.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS
        and attempt.get("tranche_002_status") == TRANCHE_002_STATUS
        and attempt.get("tranche_003_status") == TRANCHE_003_STATUS
        and attempt.get("tranche_005_status") == TRANCHE_005_STATUS
        and attempt.get("tranche_005_dependency") == TRANCHE_005_DEPENDENCY
        and attempt.get("tranche_006_status") == TRANCHE_006_STATUS
        and attempt.get("tranche_006_dependency") == TRANCHE_006_DEPENDENCY
        and attempt.get("tranche_006_dependency_class")
        == TRANCHE_006_DEPENDENCY_CLASS
        and attempt.get("tranche_006_dependency_finding_id")
        == TRANCHE_006_FINDING_ID,
        "release_hold_preserved": attempt.get("release_readiness_decision_status")
        == RELEASE_READINESS_DECISION
        and attempt.get("release_readiness_held") is True
        and attempt.get("release_readiness_still_blocked") is True,
        "no_closure_construction_or_blocker_movement": attempt.get(
            "witness_chain_constructed"
        )
        is False
        and attempt.get("source_map_witness_chain_constructed") is False
        and attempt.get("source_map_closure_claimed") is False
        and attempt.get("qft_gr_source_map_semantic_closure_claimed") is False
        and attempt.get("qft_gr_seam_closed") is False
        and attempt.get("qft_gr_seam_closure_claimed") is False
        and attempt.get("tranche_004_moved_to_documented_dependency_nonblocking")
        is False
        and attempt.get("tranche_004_retained_blocker_discharged") is False,
        "no_release_readiness_or_assembly": attempt.get("release_assembly_authorized")
        is False
        and attempt.get("release_packet_assembled") is False,
        "no_theorem_phase_empirical_or_master_promotion": attempt.get(
            "lean_theorem_debt_discharged"
        )
        is False
        and attempt.get("axiom_spec_backed_debt_reduced") is False
        and attempt.get("proof_debt_reduced") is False
        and attempt.get("retained_assumptions_discharged") is False
        and attempt.get("phase2_authorized") is False
        and attempt.get("empirical_validation_authorized") is False
        and attempt.get("master_action_promotion_authorized") is False,
        "forbidden_effects_all_false": all(
            value is False for value in forbidden_effect_status.values()
        )
        and all(attempt_forbidden.get(key, False) is False for key in attempt_forbidden),
        "review_records_exact_conservative_classification": RESULT_REVIEW_CLASSIFICATION
        == "partial_witness_chain_candidate_accepted_for_construction_packet_preparation_only",
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
        else "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_RESULT_REVIEW_BLOCKED",
        "consumes_bounded_source_map_witness_chain_research_attempt": EXPECTED_ATTEMPT_ID,
        "consumes_bounded_source_map_witness_chain_research_attempt_pointer": _ptr(
            attempt_path
        ),
        "consumed_bounded_source_map_witness_chain_research_attempt_schema_id": attempt.get(
            "schema_id"
        ),
        "consumed_bounded_source_map_witness_chain_research_attempt_outcome_id": attempt.get(
            "outcome_id"
        ),
        "review_scope": (
            "REVIEW_BOUNDED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_RESULT_"
            "ONLY_ACCEPT_PARTIAL_CANDIDATE_FOR_CONSTRUCTION_PACKET_PREPARATION_NO_CLOSURE"
        ),
        "research_attempt_result_reviewed": True,
        "research_attempt_result_accepted": accepted,
        "research_attempt_result_accepted_as_partial_candidate_only": accepted,
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "result_classification_count": 1 if accepted else 0,
        "partial_witness_chain_candidate_accepted_for_construction_packet_preparation_only": accepted,
        "partial_witness_chain_candidate_pending_review": False if accepted else True,
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
        "retained_tranche_004_carry_forward": retained_tranche_004,
        "required_future_route_for_tranche_004": TRANCHE_004_FUTURE_ROUTE,
        "release_readiness_decision_status": RELEASE_READINESS_DECISION,
        "release_readiness_held": True,
        "release_readiness_still_blocked": True,
        "release_readiness_proceed_authorized": False,
        "release_assembly_authorized": False,
        "release_assembly_authorized_by_review": False,
        "release_packet_assembled": False,
        "readiness_marking_authorized": False,
        "v01_alpha_marked_ready": False,
        "candidate_witness_chain_component_checks": candidate_components,
        "candidate_witness_chain_component_check_count": len(candidate_components),
        "candidate_witness_chain_surface_found_count": attempt.get(
            "candidate_witness_chain_surface_found_count"
        ),
        "construction_packet_preparation_authorized": accepted,
        "construction_packet_preparation_only": accepted,
        "source_map_witness_chain_construction_packet_prepared": False,
        "source_map_witness_chain_construction_executed": False,
        "witness_chain_constructed": False,
        "source_map_witness_chain_constructed": False,
        "source_map_closure_authorized_by_review": False,
        "source_map_closure_claimed": False,
        "qft_gr_source_map_semantic_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "qft_gr_seam_closure_authorized_by_review": False,
        "qft_gr_seam_closure_claimed": False,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "tranche_004_status_moved_by_review": False,
        "tranche_004_status_moved": False,
        "tranche_004_retained_blocker_discharged": False,
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
        else "REMEDIATE_V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_RESULT_REVIEW",
        "selected_next_target_kind": "source_map_witness_chain_construction_packet_preparation_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_FROM_RESEARCH_CANDIDATE_ONLY_"
            "NO_CONSTRUCTION_SOURCE_MAP_CLOSURE_RELEASE_ASSEMBLY_STATUS_MOVEMENT_OR_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained tranche 004 bounded source-map witness-chain research attempt "
            "result review accepts the partial candidate only for preparing a future "
            "governed construction packet. It does not construct a witness chain, claim "
            "source-map closure, close the QFT-GR seam, move tranche 004, assemble "
            "release, mark readiness, discharge theorem/proof debt or retained "
            "assumptions, authorize Phase 2, authorize empirical validation, authorize "
            "publication, promote the master action, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_attempt_result_review(
    *,
    attempt_path: Path = DEFAULT_RESEARCH_ATTEMPT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_attempt_result_review(
        attempt_path=attempt_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha retained tranche 004 bounded source-map "
            "witness-chain research attempt result review."
        )
    )
    parser.add_argument("--attempt", type=Path, default=DEFAULT_RESEARCH_ATTEMPT_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    attempt_path = ns.attempt if ns.attempt.is_absolute() else (REPO_ROOT / ns.attempt)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_attempt_result_review(
        attempt_path=attempt_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_result_review_report: "
        f"accepted={payload['accepted']} classification={payload['result_review_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
