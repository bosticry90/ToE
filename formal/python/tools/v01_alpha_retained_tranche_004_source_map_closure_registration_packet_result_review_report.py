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
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_closure_adjudication_report import (
    ASSEMBLE_RELEASE_PACKET_TARGET,
    BLOCKER_MOVEMENT_ADJUDICATION_TARGET,
    REFINED_AUTHORIZATION_ADJUDICATION_TARGET,
)
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_closure_registration_packet_report import (
    DEFAULT_OUT as DEFAULT_REGISTRATION_PACKET_PATH,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
    SOURCE_MAP_CLOSURE_REGISTRATION_EXECUTION_TARGET,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_"
    "RESULT_REVIEW_20260523_v0"
)
REVIEW_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_"
    "RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_"
    "RESULT_REVIEW_ACCEPTS_PACKET_AND_AUTHORIZES_CLOSURE_REGISTRATION_"
    "EXECUTION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "source_map_closure_registration_packet_accepted_closure_registration_"
    "execution_authorized_only"
)
CONSUMED_TARGET = (
    "review_v01_alpha_retained_tranche_004_source_map_closure_registration_"
    "packet_result"
)
NEXT_TARGET = SOURCE_MAP_CLOSURE_REGISTRATION_EXECUTION_TARGET

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_"
        "RESULT_REVIEW_20260523_v0.json"
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
    "source_map_closure_registration_registered_by_review",
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
                "The prepared source-map closure-registration packet is accepted "
                "for a separate bounded registration execution step only."
            ),
        },
        {
            "target": BLOCKER_MOVEMENT_ADJUDICATION_TARGET,
            "decision": "deferred",
            "reason": (
                "Blocker movement remains unavailable until after any later "
                "registration execution and governed movement-control review."
            ),
        },
        {
            "target": ASSEMBLE_RELEASE_PACKET_TARGET,
            "decision": "not_authorized",
            "reason": "Release assembly remains blocked by retained tranche 004.",
        },
        {
            "target": REFINED_AUTHORIZATION_ADJUDICATION_TARGET,
            "decision": "deferred",
            "reason": (
                "Refinement remains available if registration execution or its "
                "result review exposes a gap."
            ),
        },
    ]


def build_source_map_closure_registration_packet_result_review(
    *,
    packet_path: Path = DEFAULT_REGISTRATION_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    registration_criteria = list(packet.get("registration_criteria", []))
    evidence_chain = list(packet.get("evidence_chain", []))
    forbidden_downstream_claims = list(packet.get("forbidden_downstream_claims", []))
    reviewed_closure_requirements = list(
        packet.get("reviewed_closure_requirements", [])
    )
    reviewed_authorization_requirements = list(
        packet.get("reviewed_authorization_requirements", [])
    )
    reviewed_components = list(packet.get("reviewed_witness_chain_components", []))
    required_proof_surfaces = list(packet.get("required_proof_surfaces", []))
    required_evidence_surfaces = list(packet.get("required_evidence_surfaces", []))
    candidate_next_targets = _candidate_next_targets()
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_registration_packet": packet.get("packet_id")
        == PACKET_ID,
        "registration_packet_schema_expected": packet.get("schema_id")
        == EXPECTED_PACKET_SCHEMA_ID,
        "registration_packet_outcome_expected": packet.get("outcome_id")
        == EXPECTED_PACKET_OUTCOME,
        "registration_packet_selected_this_review": packet.get("selected_next_target")
        == CONSUMED_TARGET,
        "registration_packet_prepared_only": packet.get("accepted") is True
        and packet.get("prepared") is True
        and packet.get("packet_classification") == PACKET_CLASSIFICATION
        and packet.get("source_map_closure_registration_packet_prepared") is True
        and packet.get("source_map_closure_registration_packet_preparation_only")
        is True
        and packet.get("source_map_closure_registration_status_proposed")
        == "source_map_closure_registration_proposed_pending_packet_result_review",
        "packet_did_not_register_or_execute_closure": packet.get(
            "source_map_closure_registration_authorized"
        )
        is False
        and packet.get("source_map_closure_registration_executed") is False
        and packet.get("source_map_closure_registered") is False
        and packet.get("source_map_closure_claimed") is False
        and packet.get("source_map_closure_achieved") is False,
        "accepted_source_map_closure_authorization_carried": packet.get(
            "source_map_closure_authorization_accepted_by_review"
        )
        is True
        and packet.get(
            "source_map_closure_authorization_accepted_for_registration_packet_preparation_only"
        )
        is True
        and packet.get("source_map_closure_authorization_accepted_as_final_closure")
        is False,
        "registration_criteria_and_evidence_chain_carried": len(
            registration_criteria
        )
        == 4
        and packet.get("registration_criteria_count") == 4
        and all(row.get("satisfied_by_input") is True for row in registration_criteria)
        and len(evidence_chain) == 8
        and packet.get("evidence_chain_count") == 8
        and len(forbidden_downstream_claims) == 6
        and packet.get("forbidden_downstream_claim_count") == 6,
        "review_material_carried": len(reviewed_closure_requirements) == 7
        and packet.get("reviewed_closure_requirement_count") == 7
        and packet.get("accepted_closure_requirement_count") == 7
        and len(reviewed_authorization_requirements) == 7
        and packet.get("reviewed_authorization_requirement_count") == 7
        and packet.get("accepted_authorization_requirement_count") == 7
        and len(reviewed_components) == 7
        and packet.get("reviewed_witness_chain_component_count") == 7
        and len(required_proof_surfaces) == 7
        and packet.get("required_proof_surface_count") == 7
        and len(required_evidence_surfaces) == 6
        and packet.get("required_evidence_surface_count") == 6,
        "tranche_004_retained": packet.get("tranche_004_status")
        == TRANCHE_004_STATUS
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
        and packet.get("tranche_006_status") == TRANCHE_006_STATUS,
        "release_hold_preserved": packet.get("release_readiness_decision_status")
        == RELEASE_READINESS_DECISION
        and packet.get("release_readiness_held") is True
        and packet.get("release_readiness_still_blocked") is True
        and packet.get("release_readiness_proceed_authorized") is False,
        "no_seam_blocker_release_or_master_promotion_in_input": packet.get(
            "qft_gr_seam_closed"
        )
        is False
        and packet.get("qft_gr_seam_closure_authorized") is False
        and packet.get("qft_gr_seam_closure_claimed") is False
        and packet.get("tranche_004_status_moved") is False
        and packet.get("tranche_004_retained_blocker_discharged") is False
        and packet.get("release_assembly_authorized") is False
        and packet.get("release_packet_assembled") is False
        and packet.get("master_action_promotion_authorized") is False,
        "no_theorem_phase_empirical_publication_or_debt_promotion": packet.get(
            "lean_theorem_debt_discharged"
        )
        is False
        and packet.get("proof_debt_reduced") is False
        and packet.get("retained_assumptions_discharged") is False
        and packet.get("phase2_authorized") is False
        and packet.get("empirical_validation_authorized") is False
        and packet.get("publication_authorized") is False,
        "registration_execution_selected_only": sum(
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
            "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_"
            "PACKET_RESULT_REVIEW_BLOCKED"
        ),
        "consumes_source_map_closure_registration_packet": PACKET_ID,
        "consumes_source_map_closure_registration_packet_pointer": _ptr(packet_path),
        "consumed_source_map_closure_registration_packet_schema_id": packet.get(
            "schema_id"
        ),
        "consumed_source_map_closure_registration_packet_outcome_id": packet.get(
            "outcome_id"
        ),
        "consumed_source_map_closure_registration_packet_classification": packet.get(
            "packet_classification"
        ),
        "review_scope": (
            "REVIEW_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_"
            "RESULT_ONLY_NO_QFT_GR_SEAM_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_"
            "PROMOTION"
        ),
        "source_map_closure_registration_packet_result_reviewed": accepted,
        "source_map_closure_registration_packet_result_accepted": accepted,
        "source_map_closure_registration_packet_accepted_for_registration_execution_only": accepted,
        "source_map_closure_registration_packet_accepted_as_final_closure": False,
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "result_classification_count": 1 if accepted else 0,
        "source_map_closure_registration_packet_prepared": packet.get(
            "source_map_closure_registration_packet_prepared"
        )
        is True,
        "source_map_closure_registration_packet_preparation_only": packet.get(
            "source_map_closure_registration_packet_preparation_only"
        )
        is True,
        "source_map_closure_registration_status_proposed": packet.get(
            "source_map_closure_registration_status_proposed"
        ),
        "source_map_closure_registration_status_registered": False,
        "bounded_source_map_closure_registration_execution_authorized": accepted,
        "source_map_closure_registration_execution_authorized_by_review": accepted,
        "source_map_closure_registration_execution_authorized": accepted,
        "source_map_closure_registration_execution_target": NEXT_TARGET,
        "source_map_closure_registration_authorized": False,
        "source_map_closure_registration_executed": False,
        "source_map_closure_registered": False,
        "source_map_closure_claimed": False,
        "source_map_closure_achieved": False,
        "source_map_closure_authorized": False,
        "final_source_map_closure_authorized": False,
        "source_map_closure_result_claimed_as_final_closure": False,
        "source_map_closure_authorization_accepted_by_review": packet.get(
            "source_map_closure_authorization_accepted_by_review"
        )
        is True,
        "source_map_closure_authorization_accepted_for_registration_packet_preparation_only": packet.get(
            "source_map_closure_authorization_accepted_for_registration_packet_preparation_only"
        )
        is True,
        "source_map_closure_authorization_accepted_as_final_closure": False,
        "registration_criteria": registration_criteria,
        "registration_criteria_count": len(registration_criteria),
        "evidence_chain": evidence_chain,
        "evidence_chain_count": len(evidence_chain),
        "forbidden_downstream_claims": forbidden_downstream_claims,
        "forbidden_downstream_claim_count": len(forbidden_downstream_claims),
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
        "required_proof_surfaces": required_proof_surfaces,
        "required_proof_surface_count": len(required_proof_surfaces),
        "required_evidence_surfaces": required_evidence_surfaces,
        "required_evidence_surface_count": len(required_evidence_surfaces),
        "source_map_authorization_adjudication_result_accepted": packet.get(
            "source_map_authorization_adjudication_result_accepted"
        )
        is True,
        "witness_chain_construction_accepted": packet.get(
            "witness_chain_construction_accepted"
        )
        is True,
        "source_map_witness_chain_construction_accepted": packet.get(
            "source_map_witness_chain_construction_accepted"
        )
        is True,
        "source_map_closure_requirements_adjudicated": packet.get(
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
        "retained_tranche_004_carry_forward": packet.get(
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
        else (
            "REMEDIATE_V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_"
            "REGISTRATION_PACKET_RESULT_REVIEW"
        ),
        "selected_next_target_kind": (
            "retained_tranche_004_source_map_closure_registration_execution_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "EXECUTE_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_ONLY_"
            "NO_QFT_GR_SEAM_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained tranche 004 source-map closure registration packet "
            "result review accepts the prepared packet and authorizes only a "
            "separate bounded source-map closure-registration execution step. "
            "It does not execute registration, register or claim final source-map "
            "closure, close the QFT-GR seam, move tranche 004, assemble release, "
            "mark readiness, discharge theorem/proof debt or retained assumptions, "
            "authorize Phase 2, authorize empirical validation, authorize "
            "publication, promote the master action, or make an external-truth "
            "claim."
        ),
        "roadmap_update_required": True,
    }


def write_source_map_closure_registration_packet_result_review(
    *,
    packet_path: Path = DEFAULT_REGISTRATION_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_source_map_closure_registration_packet_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha retained tranche 004 source-map closure "
            "registration packet result review."
        )
    )
    parser.add_argument(
        "--packet",
        type=Path,
        default=DEFAULT_REGISTRATION_PACKET_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_source_map_closure_registration_packet_result_review(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_source_map_closure_registration_packet_result_review_report: "
        f"accepted={payload['accepted']} classification="
        f"{payload['result_review_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
