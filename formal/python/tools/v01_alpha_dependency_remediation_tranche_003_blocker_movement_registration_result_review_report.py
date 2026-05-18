from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_BLOCKER_MOVEMENT_REGISTRATION_"
    "RESULT_REVIEW_20260515_v0"
)
REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_BLOCKER_MOVEMENT_REGISTRATION_"
    "RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_BLOCKER_MOVEMENT_REGISTRATION_"
    "RESULT_REVIEW_ACCEPTS_DOCUMENTED_NONBLOCKING_MOVEMENT_AND_AUTHORIZES_NEXT_"
    "REMEDIATION_TRANCHE_SELECTION_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_REGISTRATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_BLOCKER_MOVEMENT_REGISTRATION_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_BLOCKER_MOVEMENT_REGISTRATION_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_REGISTRATION_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_BLOCKER_MOVEMENT_REGISTRATION_v0"
)
EXPECTED_REGISTRATION_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_BLOCKER_MOVEMENT_REGISTERED_AS_"
    "DOCUMENTED_NONBLOCKING_WITH_NO_RELEASE_PROMOTION"
)
EXPECTED_REGISTRATION_SELECTED_TARGET = (
    "review_v01_alpha_dependency_remediation_tranche_003_blocker_movement_registration_result"
)
TRANCHE_001_STATUS = "documented_dependency_nonblocking"
TRANCHE_002_STATUS = "documented_dependency_nonblocking"
SELECTED_REMEDIATION_FINDING_ID = "V01-ALPHA-DEP-REM-003"
SELECTED_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-003"
SELECTED_DEPENDENCY = "finite_transport_theorems_construct_residual_package_v0"
SELECTED_DEPENDENCY_CLASS = "lean_bridge_dependency"
LEAN_TARGET = (
    "ToeFormal.Bridges.QMSTATTransportResidualPackage."
    "finite_transport_theorems_construct_residual_package_v0"
)
EXPECTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
PROJECT_AXIOMS_USED: list[str] = []
POLICY_CLASSIFICATION = "policy_acceptable_with_documentation_requirement"
DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION = (
    "documentation_accepted_pending_tranche_003_status_adjudication"
)
STATUS_CANDIDATE = "documented_dependency_nonblocking_pending_result_review"
PREVIOUS_BLOCKER_STATUS = "release_blocking"
REGISTERED_BLOCKER_STATUS = "documented_dependency_nonblocking"
REGISTERED_MOVEMENT = "release_blocking -> documented_dependency_nonblocking"
REGISTERED_MOVEMENT_TOKEN = "release_blocking_to_documented_nonblocking_dependency"
REGISTRATION_CLASSIFICATION = (
    "blocker_movement_registered_as_documented_dependency_nonblocking_pending_result_review"
)
RESULT_REVIEW_CLASSIFICATION = (
    "documented_nonblocking_movement_accepted_next_tranche_selection_pending"
)
NEXT_TARGET = "prepare_v01_alpha_dependency_remediation_next_tranche_selection_packet"

OTHER_BLOCKER_IDS = [
    "V01-ALPHA-DEP-REM-004",
    "V01-ALPHA-DEP-REM-005",
    "V01-ALPHA-DEP-REM-006",
]

FORBIDDEN_EFFECTS = [
    "blocker_fully_remediated",
    "remediation_closure_executed",
    "broader_remediation_executed",
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "lean_theorem_debt_discharged",
    "axiom_spec_backed_debt_reduced",
    "axiom_spec_backed_debt_reduced_by_documentation",
    "proof_debt_reduced",
    "retained_assumptions_discharged",
    "theorem_discharge_authorized",
    "lane_reopen_authorized",
    "phase2_authorized",
    "seam_closure_authorized",
    "empirical_validation_authorized",
    "master_action_promotion_authorized",
    "claim_promotion_authorized",
    "computational_physics_execution_surface_opened",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _accepted_evidence(registration: dict[str, Any]) -> dict[str, Any]:
    return dict(registration.get("accepted_lean_dependency_evidence", {}))


def _documentation_surface(registration: dict[str, Any]) -> dict[str, Any]:
    return dict(registration.get("documentation_surface", {}))


def _registered_movement(registration: dict[str, Any]) -> dict[str, Any]:
    return dict(registration.get("registered_movement", {}))


def _remaining_obligations(registration: dict[str, Any]) -> list[dict[str, Any]]:
    return list(registration.get("other_release_blocking_obligations", []))


def _remaining_obligations_carried_forward(registration: dict[str, Any]) -> bool:
    rows = _remaining_obligations(registration)
    return (
        len(rows) == 3
        and [row.get("dependency_finding_id") for row in rows] == OTHER_BLOCKER_IDS
        and all(row.get("modified_by_tranche_003") is False for row in rows)
        and all(
            row.get("status_carry_forward") == "tracked_unmodified_not_audited_in_tranche_003"
            for row in rows
        )
    )


def build_result_review(
    *,
    registration_path: Path = DEFAULT_REGISTRATION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    registration = _read_json(registration_path)
    evidence = _accepted_evidence(registration)
    documentation_surface = _documentation_surface(registration)
    registered_movement = _registered_movement(registration)
    remaining_obligations = _remaining_obligations(registration)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_registration": registration.get("execution_id")
        == EXPECTED_REGISTRATION_ID,
        "registration_executed_and_accepted": registration.get("executed") is True
        and registration.get("accepted") is True,
        "registration_outcome_expected": registration.get("outcome_id")
        == EXPECTED_REGISTRATION_OUTCOME,
        "registration_selected_this_review": registration.get("selected_next_target")
        == EXPECTED_REGISTRATION_SELECTED_TARGET,
        "registered_true": registration.get("blocker_movement_registered") is True,
        "selected_tranche_expected": registration.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID,
        "selected_finding_expected": registration.get("selected_remediation_finding_id")
        == SELECTED_REMEDIATION_FINDING_ID,
        "selected_dependency_expected": registration.get("selected_dependency")
        == SELECTED_DEPENDENCY,
        "selected_dependency_class_expected": registration.get("selected_dependency_class")
        == SELECTED_DEPENDENCY_CLASS,
        "lean_audit_target_preserved": registration.get("lean_audit_target", {}).get(
            "lean_target"
        )
        == LEAN_TARGET,
        "tranche_001_documented_nonblocking_preserved": registration.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS
        and registered_movement.get("tranche_001_status") == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": registration.get(
            "tranche_002_status"
        )
        == TRANCHE_002_STATUS
        and registered_movement.get("tranche_002_status") == TRANCHE_002_STATUS,
        "registered_movement_exact": registered_movement.get("previous_status")
        == PREVIOUS_BLOCKER_STATUS
        and registered_movement.get("registered_status") == REGISTERED_BLOCKER_STATUS
        and registered_movement.get("registered_movement") == REGISTERED_MOVEMENT
        and registered_movement.get("registered_movement_token") == REGISTERED_MOVEMENT_TOKEN,
        "registered_movement_tranche_003_only": registered_movement.get(
            "selected_remediation_finding_id"
        )
        == SELECTED_REMEDIATION_FINDING_ID
        and registered_movement.get("selected_dependency") == SELECTED_DEPENDENCY
        and registered_movement.get("movement_scope") == "tranche_003_only",
        "status_candidate_preserved": registration.get("status_candidate_reviewed")
        == STATUS_CANDIDATE,
        "accepted_lean_dependency_evidence_preserved_exactly": evidence.get("parsed_axioms")
        == EXPECTED_AXIOMS
        and evidence.get("exact_axioms_or_dependencies_used") == EXPECTED_AXIOMS
        and evidence.get("standard_lean_axioms_used") == EXPECTED_AXIOMS,
        "project_axioms_used_empty": evidence.get("project_axioms_used")
        == PROJECT_AXIOMS_USED
        and evidence.get("project_axiom_count") == 0,
        "policy_classification_preserved": registration.get("policy_classification")
        == POLICY_CLASSIFICATION,
        "documentation_chain_preserved": registration.get(
            "documentation_result_review_classification"
        )
        == DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION
        and registration.get("documentation_accepted_only_as_documentation") is True
        and documentation_surface.get("exists") is True
        and documentation_surface.get("accepted_as_documentation") is True,
        "registration_was_pending_review": registration.get(
            "post_registration_result_review_required"
        )
        is True
        and registration.get("tranche_003_formal_movement_accepted") is False,
        "tranche_003_accepted_as_documented_nonblocking": REGISTERED_BLOCKER_STATUS
        == "documented_dependency_nonblocking",
        "remaining_three_obligations_carried_forward": _remaining_obligations_carried_forward(
            registration
        ),
        "no_release_packet_assembly": forbidden_effect_status["release_packet_assembled"]
        is False,
        "no_v01_readiness_marking": forbidden_effect_status["v01_alpha_marked_ready"] is False,
        "no_theorem_or_proof_debt_discharge": forbidden_effect_status[
            "lean_theorem_debt_discharged"
        ]
        is False
        and forbidden_effect_status["proof_debt_reduced"] is False
        and forbidden_effect_status["axiom_spec_backed_debt_reduced"] is False,
        "no_retained_assumption_discharge": forbidden_effect_status[
            "retained_assumptions_discharged"
        ]
        is False,
        "no_phase2_seam_empirical_or_master_action_authorization": all(
            forbidden_effect_status[key] is False
            for key in [
                "phase2_authorized",
                "seam_closure_authorized",
                "empirical_validation_authorized",
                "master_action_promotion_authorized",
            ]
        ),
        "forbidden_effects_all_false": all(
            value is False for value in forbidden_effect_status.values()
        ),
        "exactly_one_next_target_selected": NEXT_TARGET
        == "prepare_v01_alpha_dependency_remediation_next_tranche_selection_packet",
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_BLOCKER_MOVEMENT_REGISTRATION_RESULT_REVIEW_BLOCKED",
        "consumes_registration": EXPECTED_REGISTRATION_ID,
        "consumes_registration_pointer": _ptr(registration_path),
        "consumed_registration_schema_id": registration.get("schema_id"),
        "review_scope": (
            "REVIEW_TRANCHE_003_BLOCKER_MOVEMENT_REGISTRATION_RESULT_ONLY_ACCEPT_DOCUMENTED_NONBLOCKING_MOVEMENT_NO_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_001_release_blocker_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_002_release_blocker_status": TRANCHE_002_STATUS,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_REMEDIATION_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "lean_audit_target": registration.get("lean_audit_target"),
        "registered": registration.get("blocker_movement_registered") is True,
        "blocker_movement_registered": registration.get("blocker_movement_registered") is True,
        "registered_movement": {
            "selected_tranche_id": registered_movement.get("selected_tranche_id"),
            "selected_remediation_finding_id": registered_movement.get(
                "selected_remediation_finding_id"
            ),
            "selected_dependency": registered_movement.get("selected_dependency"),
            "previous_status": registered_movement.get("previous_status"),
            "registered_status": registered_movement.get("registered_status"),
            "registered_movement": registered_movement.get("registered_movement"),
            "registered_movement_token": registered_movement.get(
                "registered_movement_token"
            ),
            "movement_scope": registered_movement.get("movement_scope"),
            "registered_by_this_execution": registered_movement.get(
                "registered_by_this_execution"
            ),
            "requires_result_review_for_formal_acceptance": False,
            "tranche_001_status": registered_movement.get("tranche_001_status"),
            "tranche_002_status": registered_movement.get("tranche_002_status"),
            "global_release_readiness_effect": "none",
            "theorem_or_proof_debt_effect": "none",
            "other_blocker_effect": "none",
        },
        "accepted_lean_dependency_evidence": {
            "parsed_axioms": evidence.get("parsed_axioms"),
            "exact_axioms_or_dependencies_used": evidence.get(
                "exact_axioms_or_dependencies_used"
            ),
            "standard_lean_axioms_used": evidence.get("standard_lean_axioms_used"),
            "standard_lean_or_mathlib_axioms_used": evidence.get(
                "standard_lean_or_mathlib_axioms_used"
            ),
            "standard_lean_axiom_count": evidence.get("standard_lean_axiom_count"),
            "project_axioms_used": evidence.get("project_axioms_used"),
            "project_axiom_count": evidence.get("project_axiom_count"),
            "project_local_axioms_present": evidence.get("project_local_axioms_present"),
            "classification": evidence.get("classification"),
            "raw_output": evidence.get("raw_output"),
        },
        "policy_classification": POLICY_CLASSIFICATION,
        "documentation_result_review_classification": DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION,
        "documentation_surface": documentation_surface,
        "documentation_accepted_only_as_documentation": True,
        "status_candidate_reviewed": STATUS_CANDIDATE,
        "blocker_movement_registration_result_classification": registration.get(
            "blocker_movement_registration_result_classification"
        ),
        "blocker_movement_registration_result_review_classification": (
            RESULT_REVIEW_CLASSIFICATION
        ),
        "tranche_003_formal_movement_accepted": accepted,
        "tranche_003_release_blocker_status": REGISTERED_BLOCKER_STATUS,
        "tranche_003_dependency_policy_remediation_satisfied": accepted,
        "tranche_003_cleared_for_global_release_readiness": False,
        "global_release_readiness_still_blocked": True,
        "release_blocking_obligation_count_after_review": len(remaining_obligations),
        "remaining_release_blocking_obligation_count_after_review": len(
            remaining_obligations
        ),
        "remaining_release_blocking_obligations": remaining_obligations,
        "other_release_blocking_obligations": remaining_obligations,
        "other_release_blocking_obligation_count": len(remaining_obligations),
        "release_packet_assembled": False,
        "v01_alpha_marked_ready": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "axiom_spec_backed_debt_reduced_by_documentation": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "validation_claim_authorized": False,
        "forbidden_effect_status": forbidden_effect_status,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_BLOCKER_MOVEMENT_REGISTRATION_RESULT_REVIEW",
        "selected_next_target_kind": "next_remediation_tranche_selection_packet_preparation_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_NEXT_REMEDIATION_TRANCHE_SELECTION_PACKET_ONLY_NO_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": (
                    "Tranche 003 movement is accepted, so select the next remediation "
                    "tranche using the remaining three blockers."
                ),
            },
            {
                "target": "prepare_v01_alpha_dependency_remediation_tranche_004_execution_packet",
                "decision": "deferred",
                "reason": (
                    "Direct tranche 004 preparation is deferred until a selection packet "
                    "chooses the next tranche by the stable first-remaining-blocker rule."
                ),
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": (
                    "Release-readiness adjudication remains blocked by three release-blocking "
                    "obligations."
                ),
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 003 blocker movement registration "
            "result review accepts the documented/nonblocking movement for V01-ALPHA-DEP-REM-003 "
            "and authorizes only next remediation tranche selection. It does not assemble the "
            "release packet, mark v0.1-alpha readiness, discharge Lean theorem debt, reduce "
            "axiom/spec-backed proof debt, discharge retained assumptions, authorize Phase 2, "
            "close seams, validate empirically, promote the master action, promote claims, or "
            "make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_result_review(
    *,
    registration_path: Path = DEFAULT_REGISTRATION_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(
        registration_path=registration_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha dependency remediation tranche 003 blocker movement "
            "registration result review."
        )
    )
    parser.add_argument("--registration", type=Path, default=DEFAULT_REGISTRATION_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    registration_path = (
        ns.registration if ns.registration.is_absolute() else (REPO_ROOT / ns.registration)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        registration_path=registration_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_dependency_remediation_tranche_003_blocker_movement_registration_result_review_report: "
        f"accepted={payload['accepted']} registered={payload['registered']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
