from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_report import (
    ACCEPTED_SOURCE_MAP_CLOSURE_REGISTRATION_STATUS,
    PRIOR_TRANCHE_004_STATUS,
    PROPOSED_MOVEMENT,
    PROPOSED_TRANCHE_004_STATUS,
)
from formal.python.tools.v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_result_review_report import (
    DEFAULT_OUT as DEFAULT_PACKET_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_EXECUTION_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_PACKET_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_PACKET_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_PACKET_RESULT_REVIEW_SCHEMA_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    DEFAULT_CAPTURED_AT_UTC,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_004_DEPENDENCY,
    TRANCHE_004_FINDING_ID,
    TRANCHE_005_STATUS,
    TRANCHE_006_STATUS,
)
from formal.python.tools.v01_alpha_retained_tranche_004_release_readiness_adjudication_report import (
    RELEASE_READINESS_DECISION,
    SELECTED_TRANCHE_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_closure_registration_result_review_report import (
    SOURCE_MAP_CLOSURE_REGISTRATION_ACCEPTED_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_"
    "AFTER_SOURCE_MAP_CLOSURE_20260523_v0"
)
EXECUTION_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_"
    "AFTER_SOURCE_MAP_CLOSURE_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTERED_AFTER_"
    "SOURCE_MAP_CLOSURE_WITH_NO_SEAM_CLOSURE_OR_RELEASE_PROMOTION"
)
REGISTRATION_CLASSIFICATION = (
    "tranche_004_blocker_movement_registered_as_documented_source_map_closed_"
    "nonblocking_pending_result_review"
)
REGISTERED_TRANCHE_004_STATUS = PROPOSED_TRANCHE_004_STATUS
TRANCHE_004_STATUS_PENDING_REVIEW = (
    "documented_source_map_closed_nonblocking_pending_result_review"
)
NEXT_TARGET = (
    "review_v01_alpha_retained_tranche_004_blocker_movement_registration_"
    "after_source_map_closure_result"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_"
        "AFTER_SOURCE_MAP_CLOSURE_20260523_v0.json"
    )
)

FORBIDDEN_EFFECTS = [
    "axiom_spec_backed_debt_reduced",
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
    "release_readiness_proceed_authorized",
    "retained_assumptions_discharged",
    "tranche_004_formal_movement_accepted",
    "tranche_004_retained_blocker_discharged",
    "v01_alpha_marked_ready",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _registration_steps() -> list[dict[str, Any]]:
    return [
        {
            "step_id": "blocker_movement_execution_001_consume_packet_result_review",
            "result": "accepted_packet_result_review_consumed",
        },
        {
            "step_id": "blocker_movement_execution_002_preserve_source_map_closure_evidence",
            "result": "accepted_source_map_closure_registration_evidence_preserved",
        },
        {
            "step_id": "blocker_movement_execution_003_register_tranche_004_movement",
            "result": REGISTRATION_CLASSIFICATION,
        },
        {
            "step_id": "blocker_movement_execution_004_preserve_downstream_firewalls",
            "result": (
                "no_qft_gr_seam_closure_release_readiness_release_assembly_"
                "proof_debt_phase2_empirical_publication_or_master_action_promotion"
            ),
        },
        {
            "step_id": "blocker_movement_execution_005_select_result_review",
            "result": "blocker_movement_registration_result_review_required",
            "selected_next_target": NEXT_TARGET,
        },
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The execution registers tranche 004 movement pending result "
                "review; formal acceptance requires a separate review checkpoint."
            ),
        },
        {
            "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
            "decision": "deferred",
            "reason": (
                "Release-readiness adjudication must wait until movement "
                "registration is result-reviewed."
            ),
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "QFT-GR seam closure requires a separate downstream adjudication.",
        },
        {
            "target": "assemble_v01_alpha_release_packet",
            "decision": "not_authorized",
            "reason": "Release assembly remains unauthorized by movement execution.",
        },
        {
            "target": "mark_v01_alpha_release_ready",
            "decision": "not_authorized",
            "reason": "Release readiness remains held until separately adjudicated.",
        },
    ]


def _registered_movement() -> dict[str, Any]:
    return {
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": TRANCHE_004_FINDING_ID,
        "selected_dependency": TRANCHE_004_DEPENDENCY,
        "previous_status": PRIOR_TRANCHE_004_STATUS,
        "registered_status": REGISTERED_TRANCHE_004_STATUS,
        "status_after_execution": TRANCHE_004_STATUS_PENDING_REVIEW,
        "registered_movement": PROPOSED_MOVEMENT,
        "movement_scope": "retained_tranche_004_source_map_blocker_only",
        "registered_by_this_execution": True,
        "requires_result_review_for_formal_acceptance": True,
        "global_release_readiness_effect": "none",
        "qft_gr_seam_closure_effect": "none",
        "theorem_or_proof_debt_effect": "none",
    }


def build_blocker_movement_registration_after_source_map_closure(
    *,
    packet_result_review_path: Path = DEFAULT_PACKET_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(packet_result_review_path)
    evidence_chain = list(review.get("evidence_chain", []))
    movement_criteria = list(review.get("movement_registration_criteria", []))
    registration_criteria = list(review.get("registration_criteria", []))
    reviewed_closure_requirements = list(review.get("reviewed_closure_requirements", []))
    reviewed_authorization_requirements = list(
        review.get("reviewed_authorization_requirements", [])
    )
    reviewed_components = list(review.get("reviewed_witness_chain_components", []))
    forbidden_downstream_claims = list(review.get("forbidden_downstream_claims", []))
    source_movement_proposal = dict(review.get("movement_proposal", {}))
    registered_movement = _registered_movement()
    registration_steps = _registration_steps()
    candidate_next_targets = _candidate_next_targets()
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_packet_result_review": review.get("review_id")
        == EXPECTED_PACKET_RESULT_REVIEW_ID,
        "packet_result_review_schema_expected": review.get("schema_id")
        == EXPECTED_PACKET_RESULT_REVIEW_SCHEMA_ID,
        "packet_result_review_outcome_expected": review.get("outcome_id")
        == EXPECTED_PACKET_RESULT_REVIEW_OUTCOME,
        "packet_result_review_selected_this_execution": review.get(
            "selected_next_target"
        )
        == EXPECTED_EXECUTION_TARGET,
        "packet_result_review_authorizes_execution_only": review.get("accepted")
        is True
        and review.get("result_review_classification")
        == EXPECTED_PACKET_RESULT_REVIEW_CLASSIFICATION
        and review.get("blocker_movement_registration_execution_authorized") is True
        and review.get("blocker_movement_execution_authorized") is True
        and review.get("blocker_movement_registered") is False,
        "movement_proposal_exact": review.get("prior_tranche_004_status")
        == PRIOR_TRANCHE_004_STATUS
        and review.get("proposed_tranche_004_status") == REGISTERED_TRANCHE_004_STATUS
        and review.get("proposed_movement") == PROPOSED_MOVEMENT
        and source_movement_proposal.get("movement_scope")
        == "retained_tranche_004_source_map_blocker_only",
        "registers_only_tranche_004": registered_movement["selected_tranche_id"]
        == SELECTED_TRANCHE_ID
        and registered_movement["selected_remediation_finding_id"]
        == TRANCHE_004_FINDING_ID
        and registered_movement["movement_scope"]
        == "retained_tranche_004_source_map_blocker_only",
        "registered_movement_exact": registered_movement["previous_status"]
        == PRIOR_TRANCHE_004_STATUS
        and registered_movement["registered_status"] == REGISTERED_TRANCHE_004_STATUS
        and registered_movement["registered_movement"] == PROPOSED_MOVEMENT
        and registered_movement["status_after_execution"]
        == TRANCHE_004_STATUS_PENDING_REVIEW,
        "source_map_closure_registration_evidence_preserved": review.get(
            "accepted_source_map_closure_registration"
        )
        == ACCEPTED_SOURCE_MAP_CLOSURE_REGISTRATION_STATUS
        and review.get("source_map_closure_registration_status")
        == SOURCE_MAP_CLOSURE_REGISTRATION_ACCEPTED_STATUS
        and review.get("registered_source_map_closure_accepted_by_review") is True
        and review.get("source_map_closure_registered") is True
        and review.get("final_source_map_closure_registered") is True
        and review.get("source_map_closure_external_truth_claimed") is False,
        "evidence_and_criteria_preserved": len(evidence_chain) == 9
        and review.get("evidence_chain_count") == 9
        and len(movement_criteria) == 4
        and review.get("movement_registration_criteria_count") == 4
        and len(registration_criteria) == 4
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
        "execution_records_movement_pending_review": len(registration_steps) == 5
        and registered_movement["registered_by_this_execution"] is True
        and registered_movement["requires_result_review_for_formal_acceptance"] is True,
        "does_not_close_seam_or_promote_release": review.get("qft_gr_seam_closed")
        is False
        and review.get("qft_gr_seam_closure_authorized") is False
        and review.get("qft_gr_seam_closure_claimed") is False
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
        "execution_id": EXECUTION_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "executed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_"
            "AFTER_SOURCE_MAP_CLOSURE_BLOCKED"
        ),
        "consumes_blocker_movement_registration_packet_result_review": (
            EXPECTED_PACKET_RESULT_REVIEW_ID
        ),
        "consumes_blocker_movement_registration_packet_result_review_pointer": _ptr(
            packet_result_review_path
        ),
        "consumed_blocker_movement_registration_packet_result_review_schema_id": (
            review.get("schema_id")
        ),
        "consumed_blocker_movement_registration_packet_result_review_outcome_id": (
            review.get("outcome_id")
        ),
        "consumed_blocker_movement_registration_packet_result_review_classification": (
            review.get("result_review_classification")
        ),
        "execution_scope": (
            "EXECUTE_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_AFTER_"
            "SOURCE_MAP_CLOSURE_ONLY_NO_QFT_GR_SEAM_CLOSURE_OR_RELEASE_PROMOTION"
        ),
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": TRANCHE_004_FINDING_ID,
        "selected_dependency": TRANCHE_004_DEPENDENCY,
        "selected_dependency_class": "blocked_bridge_authorization_dependency",
        "prior_tranche_004_status": PRIOR_TRANCHE_004_STATUS,
        "registered_tranche_004_status": REGISTERED_TRANCHE_004_STATUS,
        "tranche_004_status": TRANCHE_004_STATUS_PENDING_REVIEW,
        "tranche_004_status_pending_result_review": TRANCHE_004_STATUS_PENDING_REVIEW,
        "registered_movement": registered_movement,
        "registered_movement_name": PROPOSED_MOVEMENT,
        "previous_blocker_status": PRIOR_TRANCHE_004_STATUS,
        "registered_blocker_status": REGISTERED_TRANCHE_004_STATUS,
        "accepted_source_map_closure_registration": (
            ACCEPTED_SOURCE_MAP_CLOSURE_REGISTRATION_STATUS
        ),
        "source_map_closure_registration_status": (
            SOURCE_MAP_CLOSURE_REGISTRATION_ACCEPTED_STATUS
        ),
        "registered_source_map_closure_accepted_by_review": True,
        "source_map_closure_registered": True,
        "final_source_map_closure_registered": True,
        "source_map_closure_authorized": True,
        "final_source_map_closure_authorized": True,
        "source_map_closure_achieved": True,
        "source_map_closure_claimed": False,
        "source_map_closure_external_truth_claimed": False,
        "source_map_closure_registration_external_truth_claimed": False,
        "movement_registration_criteria": movement_criteria,
        "movement_registration_criteria_count": len(movement_criteria),
        "registration_criteria": registration_criteria,
        "registration_criteria_count": len(registration_criteria),
        "evidence_chain": evidence_chain,
        "evidence_chain_count": len(evidence_chain),
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
        "blocker_movement_registration_steps": registration_steps,
        "blocker_movement_registration_step_count": len(registration_steps),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_005_status": TRANCHE_005_STATUS,
        "tranche_006_status": TRANCHE_006_STATUS,
        "documented_dependency_nonblocking_tranche_count": 5,
        "blocker_movement_registration_packet_result_reviewed": True,
        "blocker_movement_registration_packet_result_accepted": True,
        "blocker_movement_registration_execution_authorized": True,
        "blocker_movement_execution_authorized": True,
        "blocker_movement_registration_executed": accepted,
        "blocker_movement_registered": accepted,
        "blocker_movement_registration_status": TRANCHE_004_STATUS_PENDING_REVIEW,
        "blocker_movement_registration_result_classification": (
            REGISTRATION_CLASSIFICATION if accepted else "registration_blocked"
        ),
        "blocker_movement_registration_result_classification_count": (
            1 if accepted else 0
        ),
        "blocker_movement_registration_result_review_required": True,
        "blocker_movement_registration_result_review_authorized": accepted,
        "tranche_004_status_moved_by_execution": accepted,
        "tranche_004_status_moved": accepted,
        "tranche_004_moved_to_documented_source_map_closed_nonblocking": accepted,
        "tranche_004_formal_movement_accepted": False,
        "tranche_004_cleared_for_release_readiness": False,
        "tranche_004_retained_blocker_discharged": False,
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
            "REGISTRATION_AFTER_SOURCE_MAP_CLOSURE"
        ),
        "selected_next_target_kind": (
            "retained_tranche_004_blocker_movement_registration_result_review_"
            "after_source_map_closure_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_AFTER_"
            "SOURCE_MAP_CLOSURE_RESULT_ONLY_NO_QFT_GR_SEAM_CLOSURE_OR_RELEASE_"
            "PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained tranche 004 blocker-movement registration execution "
            "registers only tranche 004 movement to documented_source_map_closed_"
            "nonblocking pending result review. It preserves the accepted "
            "source-map closure registration evidence, does not close the "
            "QFT-GR seam, does not assemble release or mark readiness, does "
            "not discharge theorem/proof debt or retained assumptions, does "
            "not authorize Phase 2, empirical validation, publication, or "
            "master-action promotion, and does not make an external-truth "
            "claim."
        ),
        "roadmap_update_required": True,
    }


def write_blocker_movement_registration_after_source_map_closure(
    *,
    packet_result_review_path: Path = DEFAULT_PACKET_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_blocker_movement_registration_after_source_map_closure(
        packet_result_review_path=packet_result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha retained tranche 004 blocker movement "
            "registration execution after source-map closure."
        )
    )
    parser.add_argument(
        "--packet-result-review",
        type=Path,
        default=DEFAULT_PACKET_RESULT_REVIEW_PATH,
    )
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
    payload = write_blocker_movement_registration_after_source_map_closure(
        packet_result_review_path=packet_result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_blocker_movement_registration_"
        "after_source_map_closure_report: "
        f"accepted={payload['accepted']} classification="
        f"{payload['blocker_movement_registration_result_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
