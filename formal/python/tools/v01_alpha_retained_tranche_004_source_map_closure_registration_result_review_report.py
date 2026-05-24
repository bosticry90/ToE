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
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_closure_registration_report import (
    DEFAULT_OUT as DEFAULT_REGISTRATION_PATH,
    EXECUTION_ID as EXPECTED_REGISTRATION_EXECUTION_ID,
    OUTCOME_ID as EXPECTED_REGISTRATION_OUTCOME,
    REGISTRATION_RESULT_CLASSIFICATION as EXPECTED_REGISTRATION_CLASSIFICATION,
    SCHEMA_ID as EXPECTED_REGISTRATION_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_"
    "RESULT_REVIEW_20260523_v0"
)
REVIEW_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_"
    "RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_"
    "RESULT_REVIEW_ACCEPTS_REGISTERED_SOURCE_MAP_CLOSURE_AND_AUTHORIZES_"
    "TRANCHE_004_BLOCKER_MOVEMENT_PACKET_PREPARATION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "registered_source_map_closure_accepted_blocker_movement_packet_"
    "preparation_only"
)
CONSUMED_TARGET = (
    "review_v01_alpha_retained_tranche_004_source_map_closure_registration_result"
)
NEXT_TARGET = (
    "prepare_v01_alpha_retained_tranche_004_blocker_movement_registration_"
    "packet_after_source_map_closure"
)
SOURCE_MAP_CLOSURE_REGISTRATION_ACCEPTED_STATUS = (
    "source_map_closure_registered_result_review_accepted"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_"
        "RESULT_REVIEW_20260523_v0.json"
    )
)

FORBIDDEN_EFFECTS = [
    "axiom_spec_backed_debt_reduced",
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
                "The registered source-map closure is accepted by result review, "
                "so the only authorized next step is preparing a separate tranche "
                "004 blocker-movement registration packet."
            ),
        },
        {
            "target": BLOCKER_MOVEMENT_ADJUDICATION_TARGET,
            "decision": "deferred",
            "reason": (
                "The older movement-adjudication route is superseded here by a "
                "narrow post-source-map-closure movement-registration packet."
            ),
        },
        {
            "target": ASSEMBLE_RELEASE_PACKET_TARGET,
            "decision": "not_authorized",
            "reason": "Release assembly remains blocked until later governed review.",
        },
        {
            "target": REFINED_AUTHORIZATION_ADJUDICATION_TARGET,
            "decision": "deferred",
            "reason": (
                "Refinement remains available only if the movement-packet path "
                "exposes a registration or evidence gap."
            ),
        },
    ]


def build_source_map_closure_registration_result_review(
    *,
    registration_path: Path = DEFAULT_REGISTRATION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    registration = _read_json(registration_path)
    candidate_next_targets = _candidate_next_targets()
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    registration_criteria = list(registration.get("registration_criteria", []))
    evidence_chain = list(registration.get("evidence_chain", []))
    forbidden_downstream_claims = list(
        registration.get("forbidden_downstream_claims", [])
    )
    reviewed_closure_requirements = list(
        registration.get("reviewed_closure_requirements", [])
    )
    reviewed_authorization_requirements = list(
        registration.get("reviewed_authorization_requirements", [])
    )
    reviewed_components = list(
        registration.get("reviewed_witness_chain_components", [])
    )
    required_proof_surfaces = list(registration.get("required_proof_surfaces", []))
    required_evidence_surfaces = list(
        registration.get("required_evidence_surfaces", [])
    )
    registration_steps = list(registration.get("registration_execution_steps", []))

    acceptance_criteria = {
        "consumes_expected_registration_execution": registration.get("execution_id")
        == EXPECTED_REGISTRATION_EXECUTION_ID,
        "registration_schema_expected": registration.get("schema_id")
        == EXPECTED_REGISTRATION_SCHEMA_ID,
        "registration_outcome_expected": registration.get("outcome_id")
        == EXPECTED_REGISTRATION_OUTCOME,
        "registration_selected_this_review": registration.get("selected_next_target")
        == CONSUMED_TARGET,
        "registration_classification_expected": registration.get(
            "source_map_closure_registration_result_classification"
        )
        == EXPECTED_REGISTRATION_CLASSIFICATION
        and registration.get("source_map_closure_registration_result_classification_count")
        == 1
        and registration.get("result_classification_count") == 1,
        "registration_executed_pending_result_review": registration.get("accepted")
        is True
        and registration.get("executed") is True
        and registration.get("source_map_closure_registration_executed") is True
        and registration.get("source_map_closure_registered_pending_result_review")
        is True
        and registration.get("source_map_closure_registration_pending_result_review")
        is True
        and registration.get("source_map_closure_registration_result_review_required")
        is True,
        "registration_material_carried": len(registration_criteria) == 4
        and registration.get("registration_criteria_count") == 4
        and len(evidence_chain) == 8
        and registration.get("evidence_chain_count") == 8
        and len(forbidden_downstream_claims) == 6
        and registration.get("forbidden_downstream_claim_count") == 6
        and len(registration_steps) == 5
        and registration.get("registration_execution_step_count") == 5,
        "review_material_carried": len(reviewed_closure_requirements) == 7
        and registration.get("reviewed_closure_requirement_count") == 7
        and registration.get("accepted_closure_requirement_count") == 7
        and len(reviewed_authorization_requirements) == 7
        and registration.get("accepted_authorization_requirement_count") == 7
        and len(reviewed_components) == 7
        and registration.get("reviewed_witness_chain_component_count") == 7
        and len(required_proof_surfaces) == 7
        and len(required_evidence_surfaces) == 6,
        "tranche_004_retained_before_movement_packet": registration.get(
            "tranche_004_status"
        )
        == TRANCHE_004_STATUS
        and registration.get("retained_tranche_004_carry_forward", {}).get("status")
        == TRANCHE_004_STATUS
        and registration.get("selected_remediation_finding_id")
        == TRANCHE_004_FINDING_ID
        and registration.get("selected_dependency") == TRANCHE_004_DEPENDENCY,
        "documented_dependency_nonblocking_queue_preserved": registration.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS
        and registration.get("tranche_002_status") == TRANCHE_002_STATUS
        and registration.get("tranche_003_status") == TRANCHE_003_STATUS
        and registration.get("tranche_005_status") == TRANCHE_005_STATUS
        and registration.get("tranche_006_status") == TRANCHE_006_STATUS,
        "release_hold_preserved": registration.get("release_readiness_decision_status")
        == RELEASE_READINESS_DECISION
        and registration.get("release_readiness_held") is True
        and registration.get("release_readiness_still_blocked") is True
        and registration.get("release_readiness_proceed_authorized") is False,
        "no_seam_blocker_release_or_master_promotion_in_input": registration.get(
            "qft_gr_seam_closed"
        )
        is False
        and registration.get("qft_gr_seam_closure_authorized") is False
        and registration.get("qft_gr_seam_closure_claimed") is False
        and registration.get("tranche_004_status_moved") is False
        and registration.get("tranche_004_retained_blocker_discharged") is False
        and registration.get("release_assembly_authorized") is False
        and registration.get("release_packet_assembled") is False
        and registration.get("master_action_promotion_authorized") is False,
        "no_theorem_phase_empirical_publication_or_debt_promotion": registration.get(
            "lean_theorem_debt_discharged"
        )
        is False
        and registration.get("proof_debt_reduced") is False
        and registration.get("retained_assumptions_discharged") is False
        and registration.get("phase2_authorized") is False
        and registration.get("empirical_validation_authorized") is False
        and registration.get("publication_authorized") is False,
        "blocker_movement_packet_preparation_selected_only": sum(
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
            "RESULT_REVIEW_BLOCKED"
        ),
        "consumes_source_map_closure_registration_execution": (
            EXPECTED_REGISTRATION_EXECUTION_ID
        ),
        "consumes_source_map_closure_registration_execution_pointer": _ptr(
            registration_path
        ),
        "consumed_source_map_closure_registration_schema_id": registration.get(
            "schema_id"
        ),
        "consumed_source_map_closure_registration_outcome_id": registration.get(
            "outcome_id"
        ),
        "consumed_source_map_closure_registration_result_classification": (
            registration.get("source_map_closure_registration_result_classification")
        ),
        "review_scope": (
            "REVIEW_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_RESULT_"
            "ONLY_NO_QFT_GR_SEAM_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "source_map_closure_registration_result_reviewed": accepted,
        "source_map_closure_registration_result_accepted_by_review": accepted,
        "registered_source_map_closure_accepted_by_review": accepted,
        "registered_source_map_closure_accepted_for_blocker_movement_packet_preparation_only": accepted,
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "result_classification_count": 1 if accepted else 0,
        "source_map_closure_registration_status": (
            SOURCE_MAP_CLOSURE_REGISTRATION_ACCEPTED_STATUS
            if accepted
            else "source_map_closure_registration_result_review_rejected"
        ),
        "source_map_closure_registration_finalized_by_review": accepted,
        "source_map_closure_registered": accepted,
        "source_map_closure_registered_as_final": accepted,
        "final_source_map_closure_registered": accepted,
        "source_map_closure_authorized": accepted,
        "final_source_map_closure_authorized": accepted,
        "source_map_closure_achieved": accepted,
        "source_map_closure_claimed": False,
        "source_map_closure_result_claimed_as_final_closure": False,
        "source_map_closure_external_truth_claimed": False,
        "source_map_closure_registration_external_truth_claimed": False,
        "source_map_closure_registration_executed": (
            registration.get("source_map_closure_registration_executed") is True
        ),
        "source_map_closure_registered_pending_result_review": False,
        "source_map_closure_registration_pending_result_review": False,
        "source_map_closure_registration_result_review_required": False,
        "source_map_closure_registration_result_review_authorized": False,
        "source_map_closure_registration_result_classification": (
            EXPECTED_REGISTRATION_CLASSIFICATION
        ),
        "registration_criteria": registration_criteria,
        "registration_criteria_count": len(registration_criteria),
        "evidence_chain": evidence_chain,
        "evidence_chain_count": len(evidence_chain),
        "forbidden_downstream_claims": forbidden_downstream_claims,
        "forbidden_downstream_claim_count": len(forbidden_downstream_claims),
        "reviewed_closure_requirements": reviewed_closure_requirements,
        "reviewed_closure_requirement_count": len(reviewed_closure_requirements),
        "accepted_closure_requirement_count": registration.get(
            "accepted_closure_requirement_count"
        ),
        "reviewed_authorization_requirements": reviewed_authorization_requirements,
        "reviewed_authorization_requirement_count": len(
            reviewed_authorization_requirements
        ),
        "accepted_authorization_requirement_count": registration.get(
            "accepted_authorization_requirement_count"
        ),
        "reviewed_witness_chain_components": reviewed_components,
        "reviewed_witness_chain_component_count": len(reviewed_components),
        "required_proof_surfaces": required_proof_surfaces,
        "required_proof_surface_count": len(required_proof_surfaces),
        "required_evidence_surfaces": required_evidence_surfaces,
        "required_evidence_surface_count": len(required_evidence_surfaces),
        "registration_execution_steps": registration_steps,
        "registration_execution_step_count": len(registration_steps),
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
        "retained_tranche_004_carry_forward": registration.get(
            "retained_tranche_004_carry_forward", {}
        ),
        "required_future_route_for_tranche_004": TRANCHE_004_FUTURE_ROUTE,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "tranche_004_status_moved_by_review": False,
        "tranche_004_status_moved": False,
        "tranche_004_retained_blocker_discharged": False,
        "blocker_movement_packet_preparation_authorized": accepted,
        "blocker_movement_registration_packet_preparation_authorized": accepted,
        "blocker_movement_registration_packet_preparation_only": accepted,
        "blocker_movement_registration_packet_prepared": False,
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
            "REGISTRATION_RESULT_REVIEW"
        ),
        "selected_next_target_kind": (
            "retained_tranche_004_blocker_movement_registration_packet_"
            "preparation_after_source_map_closure_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_"
            "AFTER_SOURCE_MAP_CLOSURE_ONLY_NO_QFT_GR_SEAM_CLOSURE_OR_RELEASE_"
            "PROMOTION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The retained tranche 004 source-map closure registration result "
            "review accepts the registered source-map closure as a repo-local "
            "source-map control status and authorizes only preparation of a "
            "separate tranche 004 blocker-movement registration packet. It does "
            "not close the QFT-GR seam, move tranche 004 by review alone, "
            "assemble release, mark readiness, discharge theorem/proof debt or "
            "retained assumptions, authorize Phase 2, authorize empirical "
            "validation, authorize publication, promote the master action, or "
            "make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_source_map_closure_registration_result_review(
    *,
    registration_path: Path = DEFAULT_REGISTRATION_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_source_map_closure_registration_result_review(
        registration_path=registration_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha retained tranche 004 source-map closure "
            "registration result review."
        )
    )
    parser.add_argument(
        "--registration",
        type=Path,
        default=DEFAULT_REGISTRATION_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    registration_path = (
        ns.registration if ns.registration.is_absolute() else (REPO_ROOT / ns.registration)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_source_map_closure_registration_result_review(
        registration_path=registration_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_retained_tranche_004_source_map_closure_registration_result_review_report: "
        f"accepted={payload['accepted']} classification="
        f"{payload['result_review_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
