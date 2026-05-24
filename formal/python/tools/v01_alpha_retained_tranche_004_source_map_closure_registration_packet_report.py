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
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_closure_adjudication_result_review_report import (
    DEFAULT_OUT as DEFAULT_CLOSURE_ADJUDICATION_RESULT_REVIEW_PATH,
    OUTCOME_ID as EXPECTED_CLOSURE_ADJUDICATION_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_CLOSURE_ADJUDICATION_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_CLOSURE_ADJUDICATION_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_CLOSURE_ADJUDICATION_RESULT_REVIEW_SCHEMA_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_closure_adjudication_report import (
    ASSEMBLE_RELEASE_PACKET_TARGET,
    BLOCKER_MOVEMENT_ADJUDICATION_TARGET,
    REFINED_AUTHORIZATION_ADJUDICATION_TARGET,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_"
    "20260523_v0"
)
PACKET_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_"
    "PREPARED_WITH_NO_SEAM_CLOSURE_OR_RELEASE_PROMOTION"
)
PACKET_CLASSIFICATION = (
    "source_map_closure_registration_packet_prepared_no_seam_closure_or_"
    "release_promotion"
)
CONSUMED_TARGET = (
    "prepare_v01_alpha_retained_tranche_004_source_map_closure_registration_packet"
)
NEXT_TARGET = (
    "review_v01_alpha_retained_tranche_004_source_map_closure_registration_"
    "packet_result"
)
SOURCE_MAP_CLOSURE_REGISTRATION_EXECUTION_TARGET = (
    "execute_v01_alpha_retained_tranche_004_source_map_closure_registration"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_"
        "20260523_v0.json"
    )
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
    "source_map_closure_registration_executed",
    "tranche_004_retained_blocker_discharged",
    "tranche_004_status_moved",
    "v01_alpha_marked_ready",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _registration_criteria(review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "criterion_id": "accepted_closure_authorization_carried",
            "criterion": (
                "The packet carries the accepted source-map closure authorization "
                "from the closure adjudication result review."
            ),
            "satisfied_by_input": review.get(
                "source_map_closure_authorization_accepted_by_review"
            )
            is True,
        },
        {
            "criterion_id": "all_reviewed_closure_requirements_carried",
            "criterion": (
                "All reviewed closure requirements are carried into the proposed "
                "registration packet."
            ),
            "satisfied_by_input": review.get("accepted_closure_requirement_count") == 7,
        },
        {
            "criterion_id": "witness_and_authorization_chain_carried",
            "criterion": (
                "The witness-chain construction and source-map authorization "
                "adjudication evidence chain is preserved."
            ),
            "satisfied_by_input": review.get("witness_chain_construction_accepted")
            is True
            and review.get(
                "source_map_authorization_adjudication_result_accepted"
            )
            is True,
        },
        {
            "criterion_id": "registration_requires_packet_result_review",
            "criterion": (
                "No closure registration may occur until this packet is reviewed "
                "and a later governed registration step is authorized."
            ),
            "satisfied_by_input": True,
        },
    ]


def _evidence_chain(review: dict[str, Any]) -> list[dict[str, str]]:
    return [
        {
            "chain_id": "witness_chain_construction_packet",
            "status": "prepared_for_bounded_witness_chain_construction",
            "surface": (
                "formal/toe_formal/ToeFormal/Release/"
                "V01RetainedTranche004SourceMapWitnessChainConstructionPacketFromResearchCandidate.lean"
            ),
            "report": (
                "formal/docs/release/"
                "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_FROM_RESEARCH_CANDIDATE_20260523_v0.json"
            ),
        },
        {
            "chain_id": "witness_chain_construction_packet_result_review",
            "status": "accepted_for_bounded_witness_chain_construction_execution",
            "surface": (
                "formal/toe_formal/ToeFormal/Release/"
                "V01RetainedTranche004SourceMapWitnessChainConstructionPacketFromResearchCandidateResultReview.lean"
            ),
            "report": (
                "formal/docs/release/"
                "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_FROM_RESEARCH_CANDIDATE_RESULT_REVIEW_20260523_v0.json"
            ),
        },
        {
            "chain_id": "witness_chain_construction_execution",
            "status": "witness_chain_constructed_pending_result_review",
            "surface": (
                "formal/toe_formal/ToeFormal/Release/"
                "V01RetainedTranche004SourceMapWitnessChainConstructionFromResearchCandidate.lean"
            ),
            "report": (
                "formal/docs/release/"
                "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_FROM_RESEARCH_CANDIDATE_20260523_v0.json"
            ),
        },
        {
            "chain_id": "witness_chain_construction_result_review",
            "status": "accepted_for_source_map_authorization_adjudication_packet_preparation",
            "surface": (
                "formal/toe_formal/ToeFormal/Release/"
                "V01RetainedTranche004SourceMapWitnessChainConstructionResultReview.lean"
            ),
            "report": (
                "formal/docs/release/"
                "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_RESULT_REVIEW_20260523_v0.json"
            ),
        },
        {
            "chain_id": "source_map_authorization_adjudication_execution",
            "status": "requirements_satisfied_pending_result_review",
            "surface": (
                "formal/toe_formal/ToeFormal/Release/"
                "V01RetainedTranche004SourceMapAuthorizationAdjudication.lean"
            ),
            "report": (
                "formal/docs/release/"
                "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_20260523_v0.json"
            ),
        },
        {
            "chain_id": "source_map_authorization_adjudication_result_review",
            "status": "accepted_for_source_map_closure_adjudication_packet_preparation",
            "surface": (
                "formal/toe_formal/ToeFormal/Release/"
                "V01RetainedTranche004SourceMapAuthorizationAdjudicationResultReview.lean"
            ),
            "report": (
                "formal/docs/release/"
                "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_RESULT_REVIEW_20260523_v0.json"
            ),
        },
        {
            "chain_id": "source_map_closure_adjudication_execution",
            "status": "source_map_closure_authorized_pending_result_review",
            "surface": (
                "formal/toe_formal/ToeFormal/Release/"
                "V01RetainedTranche004SourceMapClosureAdjudication.lean"
            ),
            "report": (
                "formal/docs/release/"
                "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_20260523_v0.json"
            ),
        },
        {
            "chain_id": "source_map_closure_adjudication_result_review",
            "status": "accepted_for_source_map_closure_registration_packet_preparation",
            "surface": (
                "formal/toe_formal/ToeFormal/Release/"
                "V01RetainedTranche004SourceMapClosureAdjudicationResultReview.lean"
            ),
            "report": _ptr(DEFAULT_CLOSURE_ADJUDICATION_RESULT_REVIEW_PATH),
        },
    ]


def _forbidden_downstream_claims() -> list[dict[str, str]]:
    return [
        {
            "claim": "final_source_map_closure_registration",
            "status": "forbidden_by_packet_preparation",
        },
        {
            "claim": "qft_gr_seam_closure",
            "status": "forbidden_by_packet_preparation",
        },
        {
            "claim": "tranche_004_blocker_movement",
            "status": "forbidden_by_packet_preparation",
        },
        {
            "claim": "release_readiness_or_assembly",
            "status": "forbidden_by_packet_preparation",
        },
        {
            "claim": "theorem_or_proof_debt_discharge",
            "status": "forbidden_by_packet_preparation",
        },
        {
            "claim": "phase2_empirical_publication_or_master_action_promotion",
            "status": "forbidden_by_packet_preparation",
        },
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The prepared closure-registration packet must be reviewed before "
                "any registration execution or downstream movement can be considered."
            ),
        },
        {
            "target": SOURCE_MAP_CLOSURE_REGISTRATION_EXECUTION_TARGET,
            "decision": "deferred",
            "reason": "Registration execution requires an accepted packet result review.",
        },
        {
            "target": BLOCKER_MOVEMENT_ADJUDICATION_TARGET,
            "decision": "deferred",
            "reason": "Blocker movement remains unavailable by packet preparation alone.",
        },
        {
            "target": ASSEMBLE_RELEASE_PACKET_TARGET,
            "decision": "not_authorized",
            "reason": "Release assembly remains blocked by retained tranche 004.",
        },
        {
            "target": REFINED_AUTHORIZATION_ADJUDICATION_TARGET,
            "decision": "deferred",
            "reason": "Refinement remains available if packet review identifies a gap.",
        },
    ]


def build_source_map_closure_registration_packet(
    *,
    result_review_path: Path = DEFAULT_CLOSURE_ADJUDICATION_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(result_review_path)
    reviewed_closure_requirements = list(review.get("reviewed_closure_requirements", []))
    reviewed_authorization_requirements = list(
        review.get("reviewed_authorization_requirements", [])
    )
    reviewed_components = list(review.get("reviewed_witness_chain_components", []))
    required_proof_surfaces = list(review.get("required_proof_surfaces", []))
    required_evidence_surfaces = list(review.get("required_evidence_surfaces", []))
    registration_criteria = _registration_criteria(review)
    evidence_chain = _evidence_chain(review)
    forbidden_downstream_claims = _forbidden_downstream_claims()
    candidate_next_targets = _candidate_next_targets()
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_closure_adjudication_result_review": review.get("review_id")
        == EXPECTED_CLOSURE_ADJUDICATION_RESULT_REVIEW_ID,
        "result_review_schema_expected": review.get("schema_id")
        == EXPECTED_CLOSURE_ADJUDICATION_RESULT_REVIEW_SCHEMA_ID,
        "result_review_outcome_expected": review.get("outcome_id")
        == EXPECTED_CLOSURE_ADJUDICATION_RESULT_REVIEW_OUTCOME,
        "result_review_selected_this_packet": review.get("selected_next_target")
        == CONSUMED_TARGET,
        "closure_authorization_accepted": review.get(
            "result_review_classification"
        )
        == EXPECTED_CLOSURE_ADJUDICATION_RESULT_REVIEW_CLASSIFICATION
        and review.get("source_map_closure_authorization_accepted_by_review") is True
        and review.get(
            "source_map_closure_authorization_accepted_for_registration_packet_preparation_only"
        )
        is True,
        "prepares_registration_only": all(
            criterion["satisfied_by_input"] for criterion in registration_criteria
        ),
        "evidence_chain_carried": len(evidence_chain) == 8
        and len(reviewed_components) == 7
        and len(reviewed_authorization_requirements) == 7
        and len(reviewed_closure_requirements) == 7,
        "proof_and_evidence_surfaces_carried": len(required_proof_surfaces) == 7
        and len(required_evidence_surfaces) == 6,
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
        and review.get("tranche_006_status") == TRANCHE_006_STATUS,
        "release_hold_preserved": review.get("release_readiness_decision_status")
        == RELEASE_READINESS_DECISION
        and review.get("release_readiness_held") is True
        and review.get("release_readiness_still_blocked") is True
        and review.get("release_readiness_proceed_authorized") is False,
        "no_closure_registration_or_downstream_promotion_in_input": review.get(
            "source_map_closure_registered"
        )
        is False
        and review.get("source_map_closure_claimed") is False
        and review.get("source_map_closure_achieved") is False
        and review.get("qft_gr_seam_closed") is False
        and review.get("tranche_004_status_moved") is False
        and review.get("release_assembly_authorized") is False,
        "packet_result_review_selected_only": sum(
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
            "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_"
            "PACKET_BLOCKED"
        ),
        "consumes_source_map_closure_adjudication_result_review": (
            EXPECTED_CLOSURE_ADJUDICATION_RESULT_REVIEW_ID
        ),
        "consumes_source_map_closure_adjudication_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_source_map_closure_adjudication_result_review_schema_id": review.get(
            "schema_id"
        ),
        "consumed_source_map_closure_adjudication_result_review_outcome_id": review.get(
            "outcome_id"
        ),
        "consumed_source_map_closure_adjudication_result_review_classification": (
            review.get("result_review_classification")
        ),
        "packet_scope": (
            "PREPARE_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_"
            "ONLY_NO_QFT_GR_SEAM_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if accepted else 0,
        "source_map_closure_registration_packet_prepared": accepted,
        "source_map_closure_registration_packet_preparation_only": accepted,
        "source_map_closure_registration_status_proposed": (
            "source_map_closure_registration_proposed_pending_packet_result_review"
        ),
        "source_map_closure_registration_packet_result_review_authorized": accepted,
        "source_map_closure_registration_authorized": False,
        "source_map_closure_registration_executed": False,
        "source_map_closure_registered": False,
        "source_map_closure_claimed": False,
        "source_map_closure_achieved": False,
        "source_map_closure_authorized": False,
        "final_source_map_closure_authorized": False,
        "source_map_closure_authorization_accepted_by_review": review.get(
            "source_map_closure_authorization_accepted_by_review"
        )
        is True,
        "source_map_closure_authorization_accepted_for_registration_packet_preparation_only": (
            review.get(
                "source_map_closure_authorization_accepted_for_registration_packet_preparation_only"
            )
            is True
        ),
        "source_map_closure_authorization_accepted_as_final_closure": False,
        "source_map_closure_result_claimed_as_final_closure": False,
        "registration_criteria": registration_criteria,
        "registration_criteria_count": len(registration_criteria),
        "evidence_chain": evidence_chain,
        "evidence_chain_count": len(evidence_chain),
        "forbidden_downstream_claims": forbidden_downstream_claims,
        "forbidden_downstream_claim_count": len(forbidden_downstream_claims),
        "reviewed_closure_requirements": reviewed_closure_requirements,
        "reviewed_closure_requirement_count": len(reviewed_closure_requirements),
        "accepted_closure_requirement_count": review.get(
            "accepted_closure_requirement_count"
        ),
        "reviewed_authorization_requirements": reviewed_authorization_requirements,
        "reviewed_authorization_requirement_count": len(
            reviewed_authorization_requirements
        ),
        "accepted_authorization_requirement_count": review.get(
            "accepted_authorization_requirement_count"
        ),
        "reviewed_witness_chain_components": reviewed_components,
        "reviewed_witness_chain_component_count": len(reviewed_components),
        "required_proof_surfaces": required_proof_surfaces,
        "required_proof_surface_count": len(required_proof_surfaces),
        "required_evidence_surfaces": required_evidence_surfaces,
        "required_evidence_surface_count": len(required_evidence_surfaces),
        "source_map_authorization_adjudication_result_accepted": review.get(
            "source_map_authorization_adjudication_result_accepted"
        )
        is True,
        "witness_chain_construction_accepted": review.get(
            "witness_chain_construction_accepted"
        )
        is True,
        "source_map_witness_chain_construction_accepted": review.get(
            "source_map_witness_chain_construction_accepted"
        )
        is True,
        "source_map_closure_requirements_adjudicated": review.get(
            "source_map_closure_requirements_adjudicated"
        )
        is True,
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
            "REGISTRATION_PACKET"
        ),
        "selected_next_target_kind": (
            "retained_tranche_004_source_map_closure_registration_packet_"
            "result_review_only"
        ),
        "selection_count": 1 if accepted else 0,
        "post_registration_review_target": NEXT_TARGET,
        "next_action_scope": (
            "REVIEW_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_"
            "RESULT_ONLY_NO_QFT_GR_SEAM_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_"
            "PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained tranche 004 source-map closure registration packet "
            "prepares only proposed source-map closure registration status from "
            "accepted source-map closure authorization. It does not register or "
            "claim final source-map closure, close the QFT-GR seam, move tranche "
            "004, assemble release, mark readiness, discharge theorem/proof debt "
            "or retained assumptions, authorize Phase 2, authorize empirical "
            "validation, authorize publication, promote the master action, or "
            "make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_source_map_closure_registration_packet(
    *,
    result_review_path: Path = DEFAULT_CLOSURE_ADJUDICATION_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_source_map_closure_registration_packet(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha retained tranche 004 source-map closure "
            "registration packet."
        )
    )
    parser.add_argument(
        "--result-review",
        type=Path,
        default=DEFAULT_CLOSURE_ADJUDICATION_RESULT_REVIEW_PATH,
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
    payload = write_source_map_closure_registration_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_source_map_closure_registration_packet_report: "
        f"accepted={payload['accepted']} classification="
        f"{payload['packet_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
