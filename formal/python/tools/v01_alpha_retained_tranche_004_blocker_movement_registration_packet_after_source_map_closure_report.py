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
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_closure_registration_result_review_report import (
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_RESULT_REVIEW_SELECTED_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SOURCE_MAP_CLOSURE_REGISTRATION_ACCEPTED_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_"
    "AFTER_SOURCE_MAP_CLOSURE_20260523_v0"
)
PACKET_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_"
    "AFTER_SOURCE_MAP_CLOSURE_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_"
    "AFTER_SOURCE_MAP_CLOSURE_PREPARED_WITH_NO_SEAM_CLOSURE_OR_RELEASE_PROMOTION"
)
PACKET_CLASSIFICATION = (
    "blocker_movement_registration_packet_prepared_after_source_map_closure_"
    "no_seam_closure_or_release_promotion"
)
PRIOR_TRANCHE_004_STATUS = TRANCHE_004_STATUS
PROPOSED_TRANCHE_004_STATUS = "documented_source_map_closed_nonblocking"
ACCEPTED_SOURCE_MAP_CLOSURE_REGISTRATION_STATUS = "registered_source_map_closure_accepted"
PROPOSED_MOVEMENT = (
    "retained_release_blocking_source_map_blocker_to_"
    "documented_source_map_closed_nonblocking"
)
CONSUMED_TARGET = (
    "prepare_v01_alpha_retained_tranche_004_blocker_movement_registration_"
    "packet_after_source_map_closure"
)
NEXT_TARGET = (
    "review_v01_alpha_retained_tranche_004_blocker_movement_registration_"
    "packet_after_source_map_closure_result"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_"
        "AFTER_SOURCE_MAP_CLOSURE_20260523_v0.json"
    )
)

FORBIDDEN_EFFECTS = [
    "axiom_spec_backed_debt_reduced",
    "blocker_movement_authorized",
    "blocker_movement_registered",
    "blocker_movement_registration_execution_authorized",
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


def _movement_proposal() -> dict[str, Any]:
    return {
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": TRANCHE_004_FINDING_ID,
        "selected_dependency": TRANCHE_004_DEPENDENCY,
        "prior_status": PRIOR_TRANCHE_004_STATUS,
        "proposed_status": PROPOSED_TRANCHE_004_STATUS,
        "accepted_source_map_closure_registration": (
            ACCEPTED_SOURCE_MAP_CLOSURE_REGISTRATION_STATUS
        ),
        "proposed_movement": PROPOSED_MOVEMENT,
        "movement_scope": "retained_tranche_004_source_map_blocker_only",
        "requires_result_review_before_execution": True,
        "registers_movement_now": False,
        "moves_tranche_004_now": False,
        "clears_retained_blocker_now": False,
        "closes_qft_gr_seam_now": False,
        "marks_release_readiness_now": False,
    }


def _movement_registration_criteria() -> list[dict[str, Any]]:
    return [
        {
            "criterion_id": "source_map_closure_registration_result_review_consumed",
            "criterion": (
                "The accepted source-map closure registration result review is "
                "the only consumed authorization surface for this packet."
            ),
            "satisfied_by_input": True,
        },
        {
            "criterion_id": "tranche_004_prior_status_retained",
            "criterion": (
                "Tranche 004 remains retained_release_blocking_source_map_blocker "
                "before movement execution."
            ),
            "satisfied_by_input": True,
        },
        {
            "criterion_id": "movement_proposed_not_executed",
            "criterion": (
                "The packet proposes the movement to documented_source_map_closed_"
                "nonblocking but does not register or execute it."
            ),
            "satisfied_by_input": True,
        },
        {
            "criterion_id": "downstream_firewall_preserved",
            "criterion": (
                "QFT-GR seam closure, release readiness, release assembly, proof "
                "debt discharge, Phase 2, empirical validation, publication, and "
                "master-action promotion remain forbidden."
            ),
            "satisfied_by_input": True,
        },
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The blocker-movement registration packet must be result-reviewed "
                "before any tranche 004 status movement can be executed."
            ),
        },
        {
            "target": (
                "execute_v01_alpha_retained_tranche_004_blocker_movement_registration_"
                "after_source_map_closure"
            ),
            "decision": "deferred",
            "reason": (
                "Movement execution requires acceptance of this packet by a later "
                "result-review checkpoint."
            ),
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "QFT-GR seam closure is outside this packet scope.",
        },
        {
            "target": "assemble_v01_alpha_release_packet",
            "decision": "not_authorized",
            "reason": "Release assembly remains unauthorized by packet preparation.",
        },
    ]


def build_blocker_movement_registration_packet_after_source_map_closure(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(result_review_path)
    movement_proposal = _movement_proposal()
    movement_criteria = _movement_registration_criteria()
    candidate_next_targets = _candidate_next_targets()
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    evidence_chain = list(review.get("evidence_chain", [])) + [
        {
            "chain_id": "source_map_closure_registration_result_review",
            "report": _ptr(result_review_path),
            "surface": (
                "formal/toe_formal/ToeFormal/Release/"
                "V01RetainedTranche004SourceMapClosureRegistrationResultReview.lean"
            ),
            "status": EXPECTED_RESULT_REVIEW_CLASSIFICATION,
        }
    ]
    reviewed_closure_requirements = list(review.get("reviewed_closure_requirements", []))
    reviewed_authorization_requirements = list(
        review.get("reviewed_authorization_requirements", [])
    )
    reviewed_components = list(review.get("reviewed_witness_chain_components", []))
    registration_criteria = list(review.get("registration_criteria", []))
    forbidden_downstream_claims = list(review.get("forbidden_downstream_claims", []))

    acceptance_criteria = {
        "consumes_expected_source_map_closure_registration_result_review": review.get(
            "review_id"
        )
        == EXPECTED_RESULT_REVIEW_ID,
        "source_map_closure_registration_result_review_accepted": review.get(
            "accepted"
        )
        is True,
        "source_map_closure_registration_result_review_outcome_expected": review.get(
            "outcome_id"
        )
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "source_map_closure_registration_result_review_selected_this_packet": review.get(
            "selected_next_target"
        )
        == EXPECTED_RESULT_REVIEW_SELECTED_TARGET,
        "registered_source_map_closure_accepted": review.get(
            "result_review_classification"
        )
        == EXPECTED_RESULT_REVIEW_CLASSIFICATION
        and review.get("registered_source_map_closure_accepted_by_review") is True
        and review.get(
            "registered_source_map_closure_accepted_for_blocker_movement_packet_preparation_only"
        )
        is True
        and review.get("source_map_closure_registration_status")
        == SOURCE_MAP_CLOSURE_REGISTRATION_ACCEPTED_STATUS,
        "review_authorized_packet_preparation_only": review.get(
            "blocker_movement_registration_packet_preparation_authorized"
        )
        is True
        and review.get("blocker_movement_registration_packet_preparation_only") is True
        and review.get("blocker_movement_registration_packet_prepared") is False,
        "source_map_registration_accepted_without_external_truth_or_seam_claim": review.get(
            "source_map_closure_registered"
        )
        is True
        and review.get("final_source_map_closure_registered") is True
        and review.get("source_map_closure_claimed") is False
        and review.get("source_map_closure_external_truth_claimed") is False
        and review.get("qft_gr_source_map_semantic_closure_claimed") is False,
        "tranche_004_prior_status_retained": review.get("tranche_004_status")
        == PRIOR_TRANCHE_004_STATUS
        and review.get("retained_tranche_004_carry_forward", {}).get("status")
        == PRIOR_TRANCHE_004_STATUS
        and review.get("selected_remediation_finding_id") == TRANCHE_004_FINDING_ID
        and review.get("selected_dependency") == TRANCHE_004_DEPENDENCY,
        "movement_proposal_is_conservative_and_unexecuted": movement_proposal[
            "prior_status"
        ]
        == PRIOR_TRANCHE_004_STATUS
        and movement_proposal["proposed_status"] == PROPOSED_TRANCHE_004_STATUS
        and movement_proposal["proposed_movement"] == PROPOSED_MOVEMENT
        and movement_proposal["requires_result_review_before_execution"] is True
        and movement_proposal["registers_movement_now"] is False
        and movement_proposal["moves_tranche_004_now"] is False,
        "evidence_chain_preserved_and_extended": len(review.get("evidence_chain", []))
        == 8
        and len(evidence_chain) == 9
        and evidence_chain[-1]["chain_id"]
        == "source_map_closure_registration_result_review",
        "review_material_preserved": len(registration_criteria) == 4
        and review.get("registration_criteria_count") == 4
        and len(reviewed_closure_requirements) == 7
        and review.get("accepted_closure_requirement_count") == 7
        and len(reviewed_authorization_requirements) == 7
        and review.get("accepted_authorization_requirement_count") == 7
        and len(reviewed_components) == 7
        and review.get("reviewed_witness_chain_component_count") == 7
        and len(forbidden_downstream_claims) == 6,
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
        "does_not_move_tranche_004_by_preparation": review.get(
            "tranche_004_status_moved"
        )
        is False
        and review.get("tranche_004_retained_blocker_discharged") is False
        and review.get("blocker_movement_registered") is False,
        "does_not_close_seam_or_promote_release": review.get("qft_gr_seam_closed")
        is False
        and review.get("qft_gr_seam_closure_authorized") is False
        and review.get("release_assembly_authorized") is False
        and review.get("release_packet_assembled") is False
        and review.get("v01_alpha_marked_ready") is False,
        "does_not_discharge_debt_or_promote_science_program": review.get(
            "lean_theorem_debt_discharged"
        )
        is False
        and review.get("proof_debt_reduced") is False
        and review.get("retained_assumptions_discharged") is False
        and review.get("phase2_authorized") is False
        and review.get("empirical_validation_authorized") is False
        and review.get("publication_authorized") is False
        and review.get("master_action_promotion_authorized") is False,
        "movement_registration_criteria_defined": len(movement_criteria) == 4
        and all(row["satisfied_by_input"] is True for row in movement_criteria),
        "exactly_one_next_target_selected": sum(
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
            "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_"
            "PACKET_AFTER_SOURCE_MAP_CLOSURE_BLOCKED"
        ),
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if accepted else 0,
        "consumes_source_map_closure_registration_result_review": (
            EXPECTED_RESULT_REVIEW_ID
        ),
        "consumes_source_map_closure_registration_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_source_map_closure_registration_result_review_outcome_id": review.get(
            "outcome_id"
        ),
        "consumed_source_map_closure_registration_result_review_classification": (
            review.get("result_review_classification")
        ),
        "packet_scope": (
            "PREPARE_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_"
            "AFTER_SOURCE_MAP_CLOSURE_ONLY_NO_QFT_GR_SEAM_CLOSURE_OR_RELEASE_"
            "PROMOTION"
        ),
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": TRANCHE_004_FINDING_ID,
        "selected_dependency": TRANCHE_004_DEPENDENCY,
        "selected_dependency_class": "blocked_bridge_authorization_dependency",
        "prior_tranche_004_status": PRIOR_TRANCHE_004_STATUS,
        "proposed_tranche_004_status": PROPOSED_TRANCHE_004_STATUS,
        "accepted_source_map_closure_registration": (
            ACCEPTED_SOURCE_MAP_CLOSURE_REGISTRATION_STATUS
        ),
        "source_map_closure_registration_status": (
            SOURCE_MAP_CLOSURE_REGISTRATION_ACCEPTED_STATUS
        ),
        "registered_source_map_closure_accepted_by_review": accepted,
        "registered_source_map_closure_accepted_for_blocker_movement_packet_preparation_only": accepted,
        "source_map_closure_registered": True,
        "final_source_map_closure_registered": True,
        "source_map_closure_authorized": True,
        "final_source_map_closure_authorized": True,
        "source_map_closure_achieved": True,
        "source_map_closure_claimed": False,
        "source_map_closure_external_truth_claimed": False,
        "source_map_closure_registration_external_truth_claimed": False,
        "movement_proposal": movement_proposal,
        "proposed_movement": PROPOSED_MOVEMENT,
        "movement_registration_inputs": [
            "registered_source_map_closure_accepted_by_review",
            "source_map_closure_registration_status = source_map_closure_registered_result_review_accepted",
            "tranche_004 prior status = retained_release_blocking_source_map_blocker",
            "proposed status = documented_source_map_closed_nonblocking",
            "evidence chain preserved through source-map closure registration result review",
            "downstream seam/release/proof/promotion firewalls remain closed",
        ],
        "movement_registration_criteria": movement_criteria,
        "movement_registration_criteria_count": len(movement_criteria),
        "movement_registration_failure_criteria": [
            {
                "failure_id": "movement_execution_attempted_by_packet",
                "required_result": "fail_closed_before_tranche_status_change",
            },
            {
                "failure_id": "qft_gr_seam_closure_inferred_from_source_map_registration",
                "required_result": "fail_closed_no_seam_closure_claim",
            },
            {
                "failure_id": "release_readiness_or_assembly_inferred",
                "required_result": "fail_closed_release_hold_continues",
            },
            {
                "failure_id": "proof_debt_or_external_truth_claim_inferred",
                "required_result": "fail_closed_no_debt_or_external_truth_claim",
            },
        ],
        "evidence_chain": evidence_chain,
        "evidence_chain_count": len(evidence_chain),
        "registration_criteria": registration_criteria,
        "registration_criteria_count": len(registration_criteria),
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
        "forbidden_downstream_claims": forbidden_downstream_claims,
        "forbidden_downstream_claim_count": len(forbidden_downstream_claims),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_004_status": PRIOR_TRANCHE_004_STATUS,
        "tranche_005_status": TRANCHE_005_STATUS,
        "tranche_006_status": TRANCHE_006_STATUS,
        "documented_dependency_nonblocking_tranche_count": 5,
        "retained_tranche_004_carry_forward": review.get(
            "retained_tranche_004_carry_forward", {}
        ),
        "required_future_route_for_tranche_004": TRANCHE_004_FUTURE_ROUTE,
        "blocker_movement_registration_packet_prepared": accepted,
        "blocker_movement_registration_packet_prepared_after_source_map_closure": (
            accepted
        ),
        "blocker_movement_registration_packet_result_review_required": True,
        "blocker_movement_registration_packet_result_review_authorized": accepted,
        "blocker_movement_registration_execution_authorized": False,
        "blocker_movement_authorized": False,
        "blocker_movement_registered": False,
        "tranche_004_status_moved_by_packet": False,
        "tranche_004_status_moved": False,
        "tranche_004_retained_blocker_discharged": False,
        "tranche_004_moved_to_documented_source_map_closed_nonblocking": False,
        "qft_gr_source_map_semantic_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "qft_gr_seam_closure_authorized": False,
        "qft_gr_seam_closure_claimed": False,
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
            "REMEDIATE_V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_"
            "REGISTRATION_PACKET_AFTER_SOURCE_MAP_CLOSURE"
        ),
        "selected_next_target_kind": (
            "retained_tranche_004_blocker_movement_registration_packet_after_"
            "source_map_closure_result_review_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_"
            "AFTER_SOURCE_MAP_CLOSURE_RESULT_ONLY_NO_QFT_GR_SEAM_CLOSURE_OR_"
            "RELEASE_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained tranche 004 blocker-movement registration packet "
            "prepares a proposed movement from retained_release_blocking_"
            "source_map_blocker to documented_source_map_closed_nonblocking "
            "after accepted source-map closure registration. It does not move "
            "tranche 004 by packet preparation alone, close the QFT-GR seam, "
            "assemble release, mark readiness, discharge theorem/proof debt or "
            "retained assumptions, authorize Phase 2, authorize empirical "
            "validation, authorize publication, promote the master action, or "
            "make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_blocker_movement_registration_packet_after_source_map_closure(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_blocker_movement_registration_packet_after_source_map_closure(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha retained tranche 004 blocker movement "
            "registration packet after source-map closure."
        )
    )
    parser.add_argument(
        "--result-review",
        type=Path,
        default=DEFAULT_RESULT_REVIEW_PATH,
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
    payload = write_blocker_movement_registration_packet_after_source_map_closure(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_blocker_movement_registration_packet_"
        "after_source_map_closure_report: "
        f"accepted={payload['accepted']} classification="
        f"{payload['packet_classification']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
