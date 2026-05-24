from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_report import (
    ACCEPTED_SOURCE_MAP_CLOSURE_REGISTRATION_STATUS,
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    PRIOR_TRANCHE_004_STATUS,
    PROPOSED_MOVEMENT,
    PROPOSED_TRANCHE_004_STATUS,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    DEFAULT_CAPTURED_AT_UTC,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_004_DEPENDENCY,
    TRANCHE_004_FINDING_ID,
    TRANCHE_004_FUTURE_ROUTE,
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
    "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_"
    "AFTER_SOURCE_MAP_CLOSURE_RESULT_REVIEW_20260523_v0"
)
REVIEW_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_"
    "AFTER_SOURCE_MAP_CLOSURE_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_"
    "RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_BLOCKER_MOVEMENT_EXECUTION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "blocker_movement_registration_packet_accepted_after_source_map_closure_"
    "blocker_movement_execution_authorized_only"
)
CONSUMED_TARGET = (
    "review_v01_alpha_retained_tranche_004_blocker_movement_registration_"
    "packet_after_source_map_closure_result"
)
NEXT_TARGET = (
    "execute_v01_alpha_retained_tranche_004_blocker_movement_registration_"
    "after_source_map_closure"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_"
        "AFTER_SOURCE_MAP_CLOSURE_RESULT_REVIEW_20260523_v0.json"
    )
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


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The blocker-movement registration packet is accepted, so the "
                "only authorized next action is bounded registration execution."
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
            "reason": "Release assembly remains blocked after packet result review.",
        },
        {
            "target": "mark_v01_alpha_release_ready",
            "decision": "not_authorized",
            "reason": "Release readiness remains held until separately adjudicated.",
        },
    ]


def build_blocker_movement_registration_packet_result_review_after_source_map_closure(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    candidate_next_targets = _candidate_next_targets()
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    movement_proposal = dict(packet.get("movement_proposal", {}))
    movement_criteria = list(packet.get("movement_registration_criteria", []))
    evidence_chain = list(packet.get("evidence_chain", []))
    registration_criteria = list(packet.get("registration_criteria", []))
    reviewed_closure_requirements = list(packet.get("reviewed_closure_requirements", []))
    reviewed_authorization_requirements = list(
        packet.get("reviewed_authorization_requirements", [])
    )
    reviewed_components = list(packet.get("reviewed_witness_chain_components", []))
    forbidden_downstream_claims = list(packet.get("forbidden_downstream_claims", []))

    acceptance_criteria = {
        "consumes_expected_blocker_movement_registration_packet": packet.get(
            "packet_id"
        )
        == EXPECTED_PACKET_ID,
        "packet_schema_expected": packet.get("schema_id") == EXPECTED_PACKET_SCHEMA_ID,
        "packet_outcome_expected": packet.get("outcome_id") == EXPECTED_PACKET_OUTCOME,
        "packet_selected_this_review": packet.get("selected_next_target")
        == CONSUMED_TARGET,
        "packet_classification_expected": packet.get("packet_classification")
        == EXPECTED_PACKET_CLASSIFICATION
        and packet.get("packet_classification_count") == 1,
        "packet_prepared_only": packet.get("accepted") is True
        and packet.get("prepared") is True
        and packet.get("blocker_movement_registration_packet_prepared") is True
        and packet.get(
            "blocker_movement_registration_packet_prepared_after_source_map_closure"
        )
        is True
        and packet.get("blocker_movement_registration_packet_result_review_required")
        is True
        and packet.get("blocker_movement_registration_execution_authorized") is False,
        "source_map_closure_registration_previously_accepted": packet.get(
            "accepted_source_map_closure_registration"
        )
        == ACCEPTED_SOURCE_MAP_CLOSURE_REGISTRATION_STATUS
        and packet.get("source_map_closure_registration_status")
        == SOURCE_MAP_CLOSURE_REGISTRATION_ACCEPTED_STATUS
        and packet.get("registered_source_map_closure_accepted_by_review") is True,
        "source_map_registration_not_promoted_to_seam_or_external_truth": packet.get(
            "source_map_closure_registered"
        )
        is True
        and packet.get("final_source_map_closure_registered") is True
        and packet.get("source_map_closure_claimed") is False
        and packet.get("source_map_closure_external_truth_claimed") is False
        and packet.get("source_map_closure_registration_external_truth_claimed")
        is False,
        "tranche_004_prior_status_still_retained": packet.get("tranche_004_status")
        == PRIOR_TRANCHE_004_STATUS
        and packet.get("prior_tranche_004_status") == PRIOR_TRANCHE_004_STATUS
        and packet.get("retained_tranche_004_carry_forward", {}).get("status")
        == PRIOR_TRANCHE_004_STATUS,
        "proposed_movement_narrow_and_exact": packet.get("proposed_tranche_004_status")
        == PROPOSED_TRANCHE_004_STATUS
        and packet.get("proposed_movement") == PROPOSED_MOVEMENT
        and movement_proposal.get("proposed_status") == PROPOSED_TRANCHE_004_STATUS
        and movement_proposal.get("proposed_movement") == PROPOSED_MOVEMENT
        and movement_proposal.get("movement_scope")
        == "retained_tranche_004_source_map_blocker_only",
        "packet_did_not_move_or_clear_tranche_004": packet.get(
            "tranche_004_status_moved_by_packet"
        )
        is False
        and packet.get("tranche_004_status_moved") is False
        and packet.get("tranche_004_retained_blocker_discharged") is False
        and packet.get("blocker_movement_registered") is False
        and movement_proposal.get("registers_movement_now") is False
        and movement_proposal.get("moves_tranche_004_now") is False
        and movement_proposal.get("clears_retained_blocker_now") is False,
        "evidence_chain_and_review_material_preserved": len(evidence_chain) == 9
        and packet.get("evidence_chain_count") == 9
        and len(registration_criteria) == 4
        and packet.get("registration_criteria_count") == 4
        and len(movement_criteria) == 4
        and packet.get("movement_registration_criteria_count") == 4
        and len(reviewed_closure_requirements) == 7
        and packet.get("accepted_closure_requirement_count") == 7
        and len(reviewed_authorization_requirements) == 7
        and packet.get("accepted_authorization_requirement_count") == 7
        and len(reviewed_components) == 7
        and packet.get("reviewed_witness_chain_component_count") == 7
        and len(forbidden_downstream_claims) == 6,
        "documented_dependency_nonblocking_queue_preserved": packet.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS
        and packet.get("tranche_002_status") == TRANCHE_002_STATUS
        and packet.get("tranche_003_status") == TRANCHE_003_STATUS
        and packet.get("tranche_005_status") == TRANCHE_005_STATUS
        and packet.get("tranche_006_status") == TRANCHE_006_STATUS,
        "release_hold_preserved": packet.get("release_readiness_decision_status")
        == RELEASE_READINESS_DECISION
        and packet.get("release_readiness_held") is True
        and packet.get("release_readiness_still_blocked") is True
        and packet.get("release_readiness_proceed_authorized") is False,
        "does_not_close_seam_or_promote_release": packet.get("qft_gr_seam_closed")
        is False
        and packet.get("qft_gr_seam_closure_authorized") is False
        and packet.get("qft_gr_seam_closure_claimed") is False
        and packet.get("release_assembly_authorized") is False
        and packet.get("release_packet_assembled") is False
        and packet.get("v01_alpha_marked_ready") is False,
        "does_not_discharge_debt_or_promote_science_program": packet.get(
            "lean_theorem_debt_discharged"
        )
        is False
        and packet.get("proof_debt_reduced") is False
        and packet.get("retained_assumptions_discharged") is False
        and packet.get("phase2_authorized") is False
        and packet.get("empirical_validation_authorized") is False
        and packet.get("publication_authorized") is False
        and packet.get("master_action_promotion_authorized") is False,
        "authorizes_blocker_movement_execution_only": sum(
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
        else (
            "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_"
            "PACKET_AFTER_SOURCE_MAP_CLOSURE_RESULT_REVIEW_BLOCKED"
        ),
        "consumes_blocker_movement_registration_packet": EXPECTED_PACKET_ID,
        "consumes_blocker_movement_registration_packet_pointer": _ptr(packet_path),
        "consumed_blocker_movement_registration_packet_schema_id": packet.get(
            "schema_id"
        ),
        "consumed_blocker_movement_registration_packet_outcome_id": packet.get(
            "outcome_id"
        ),
        "consumed_blocker_movement_registration_packet_classification": packet.get(
            "packet_classification"
        ),
        "review_scope": (
            "REVIEW_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_"
            "AFTER_SOURCE_MAP_CLOSURE_RESULT_ONLY_AUTHORIZE_EXECUTION_NO_QFT_GR_"
            "SEAM_CLOSURE_OR_RELEASE_PROMOTION"
        ),
        "blocker_movement_registration_packet_result_reviewed": accepted,
        "blocker_movement_registration_packet_result_accepted": accepted,
        "blocker_movement_registration_packet_accepted_for_execution_only": accepted,
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "result_classification_count": 1 if accepted else 0,
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
        "registered_source_map_closure_accepted_by_review": True,
        "source_map_closure_registered": True,
        "final_source_map_closure_registered": True,
        "source_map_closure_authorized": True,
        "final_source_map_closure_authorized": True,
        "source_map_closure_achieved": True,
        "source_map_closure_claimed": False,
        "source_map_closure_external_truth_claimed": False,
        "source_map_closure_registration_external_truth_claimed": False,
        "movement_proposal": {
            "selected_tranche_id": movement_proposal.get("selected_tranche_id"),
            "selected_remediation_finding_id": movement_proposal.get(
                "selected_remediation_finding_id"
            ),
            "selected_dependency": movement_proposal.get("selected_dependency"),
            "prior_status": movement_proposal.get("prior_status"),
            "proposed_status": movement_proposal.get("proposed_status"),
            "accepted_source_map_closure_registration": movement_proposal.get(
                "accepted_source_map_closure_registration"
            ),
            "proposed_movement": movement_proposal.get("proposed_movement"),
            "movement_scope": movement_proposal.get("movement_scope"),
            "requires_result_review_before_execution": movement_proposal.get(
                "requires_result_review_before_execution"
            ),
            "registers_movement_now": False,
            "moves_tranche_004_now": False,
            "clears_retained_blocker_now": False,
            "closes_qft_gr_seam_now": False,
            "marks_release_readiness_now": False,
        },
        "proposed_movement": PROPOSED_MOVEMENT,
        "proposed_movement_accepted": accepted,
        "movement_registration_criteria": movement_criteria,
        "movement_registration_criteria_count": len(movement_criteria),
        "evidence_chain": evidence_chain,
        "evidence_chain_count": len(evidence_chain),
        "registration_criteria": registration_criteria,
        "registration_criteria_count": len(registration_criteria),
        "reviewed_closure_requirements": reviewed_closure_requirements,
        "reviewed_closure_requirement_count": len(reviewed_closure_requirements),
        "accepted_closure_requirement_count": packet.get(
            "accepted_closure_requirement_count"
        ),
        "reviewed_authorization_requirements": reviewed_authorization_requirements,
        "reviewed_authorization_requirement_count": len(
            reviewed_authorization_requirements
        ),
        "accepted_authorization_requirement_count": packet.get(
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
        "retained_tranche_004_carry_forward": packet.get(
            "retained_tranche_004_carry_forward", {}
        ),
        "required_future_route_for_tranche_004": TRANCHE_004_FUTURE_ROUTE,
        "blocker_movement_registration_packet_prepared": True,
        "blocker_movement_registration_packet_result_review_required": False,
        "blocker_movement_registration_packet_result_review_authorized": False,
        "blocker_movement_registration_execution_authorized": accepted,
        "blocker_movement_execution_authorized": accepted,
        "blocker_movement_authorized": False,
        "blocker_movement_registered": False,
        "tranche_004_status_moved_by_review": False,
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
            "REGISTRATION_PACKET_AFTER_SOURCE_MAP_CLOSURE_RESULT_REVIEW"
        ),
        "selected_next_target_kind": (
            "retained_tranche_004_blocker_movement_registration_execution_"
            "after_source_map_closure_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "EXECUTE_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_AFTER_"
            "SOURCE_MAP_CLOSURE_ONLY_NO_QFT_GR_SEAM_CLOSURE_OR_RELEASE_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained tranche 004 blocker-movement registration packet result "
            "review accepts the prepared packet and authorizes only bounded "
            "blocker-movement registration execution. It does not move tranche "
            "004 by review alone, close the QFT-GR seam, assemble release, mark "
            "readiness, discharge theorem/proof debt or retained assumptions, "
            "authorize Phase 2, authorize empirical validation, authorize "
            "publication, promote the master action, or make an external-truth "
            "claim."
        ),
        "roadmap_update_required": True,
    }


def write_blocker_movement_registration_packet_result_review_after_source_map_closure(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_blocker_movement_registration_packet_result_review_after_source_map_closure(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha retained tranche 004 blocker movement "
            "registration packet result review after source-map closure."
        )
    )
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_blocker_movement_registration_packet_result_review_after_source_map_closure(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_blocker_movement_registration_packet_"
        "after_source_map_closure_result_review_report: "
        f"accepted={payload['accepted']} classification="
        f"{payload['result_review_classification']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
