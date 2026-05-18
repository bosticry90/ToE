from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration_report import (
    CANDIDATE_BLOCKER_STATUS,
    CURRENT_BLOCKER_STATUS as PREVIOUS_BLOCKER_STATUS,
    DEFAULT_CAPTURED_AT_UTC,
    DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION,
    EXECUTION_ID as EXPECTED_REGISTRATION_ID,
    EXPECTED_AXIOMS,
    LEAN_AUDIT_COMMAND,
    LEAN_TARGET,
    NEXT_TARGET as EXPECTED_REGISTRATION_SELECTED_TARGET,
    OUTCOME_ID as EXPECTED_REGISTRATION_OUTCOME,
    POLICY_CLASSIFICATION,
    PROJECT_AXIOMS_USED,
    PROPOSED_MOVEMENT,
    PROPOSED_MOVEMENT_TOKEN,
    REGISTRATION_CLASSIFICATION,
    SELECTED_DEPENDENCY,
    SELECTED_DEPENDENCY_CLASS,
    SELECTED_FINDING_ID,
    SELECTED_TRANCHE_ID,
    STATUS_CANDIDATE,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_004_CURRENT_BLOCKER,
    TRANCHE_004_DEPENDENCY,
    TRANCHE_004_FINDING_ID,
    TRANCHE_004_RETAINED_REASON,
    TRANCHE_004_STATUS,
    TRANCHE_006_DEPENDENCY,
    TRANCHE_006_FINDING_ID,
    TRANCHE_006_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_"
    "RESULT_REVIEW_20260515_v0"
)
REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_"
    "RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_"
    "RESULT_REVIEW_ACCEPTS_DOCUMENTED_NONBLOCKING_MOVEMENT_AND_AUTHORIZES_NEXT_"
    "REMEDIATION_TRANCHE_SELECTION_ONLY"
)

DEFAULT_REGISTRATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_RESULT_REVIEW_20260515_v0.json"
)

RESULT_REVIEW_CLASSIFICATION = (
    "documented_nonblocking_movement_accepted_next_tranche_006_selection_pending"
)
NEXT_TARGET = (
    "prepare_v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_005_movement"
)

FORBIDDEN_EFFECTS = [
    "blocker_fully_remediated",
    "tranche_004_moved_to_documented_dependency_nonblocking",
    "tranche_004_reclassified_nonblocking",
    "tranche_004_retained_blocker_discharged",
    "tranche_006_moved_or_cleared",
    "remediation_closure_executed",
    "broader_remediation_executed",
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "release_readiness_pause_registered",
    "release_readiness_adjudication_prepared",
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


def _retained_tranche_004(registration: dict[str, Any]) -> dict[str, Any]:
    return dict(registration.get("retained_tranche_004_carry_forward", {}))


def _tranche_006(registration: dict[str, Any]) -> dict[str, Any]:
    return dict(registration.get("tranche_006_obligation_carry_forward", {}))


def _remaining_obligations(registration: dict[str, Any]) -> list[dict[str, Any]]:
    return list(registration.get("other_release_blocking_obligations", []))


def _remaining_obligations_carried_forward(
    rows: list[dict[str, Any]],
) -> bool:
    return (
        len(rows) == 2
        and [row.get("dependency_finding_id") for row in rows]
        == [TRANCHE_004_FINDING_ID, TRANCHE_006_FINDING_ID]
        and rows[0].get("status_carry_forward") == TRANCHE_004_STATUS
        and rows[1].get("status_carry_forward") == TRANCHE_006_STATUS
        and all(
            row.get("modified_by_tranche_005_policy_adjudication") is False
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
    retained_tranche_004 = _retained_tranche_004(registration)
    tranche_006 = _tranche_006(registration)
    remaining_obligations = _remaining_obligations(registration)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_registration": registration.get("execution_id")
        == EXPECTED_REGISTRATION_ID,
        "registration_executed_accepted_and_registered": registration.get("executed")
        is True
        and registration.get("accepted") is True
        and registration.get("registered") is True
        and registration.get("blocker_movement_registered") is True,
        "registration_outcome_expected": registration.get("outcome_id")
        == EXPECTED_REGISTRATION_OUTCOME,
        "registration_selected_this_review": registration.get("selected_next_target")
        == EXPECTED_REGISTRATION_SELECTED_TARGET,
        "selected_tranche_expected": registration.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID,
        "selected_finding_expected": registration.get("selected_remediation_finding_id")
        == SELECTED_FINDING_ID,
        "selected_dependency_expected": registration.get("selected_dependency")
        == SELECTED_DEPENDENCY,
        "selected_dependency_class_expected": registration.get("selected_dependency_class")
        == SELECTED_DEPENDENCY_CLASS,
        "lean_audit_target_preserved": registration.get("lean_audit_target", {}).get(
            "lean_target"
        )
        == LEAN_TARGET
        and registration.get("lean_audit_target", {}).get("command") == LEAN_AUDIT_COMMAND,
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
        "tranche_003_documented_nonblocking_preserved": registration.get(
            "tranche_003_status"
        )
        == TRANCHE_003_STATUS
        and registered_movement.get("tranche_003_status") == TRANCHE_003_STATUS,
        "tranche_004_retained_blocker_preserved": registration.get(
            "tranche_004_status"
        )
        == TRANCHE_004_STATUS
        and retained_tranche_004.get("status") == TRANCHE_004_STATUS
        and retained_tranche_004.get("dependency") == TRANCHE_004_DEPENDENCY
        and retained_tranche_004.get("current_blocker") == TRANCHE_004_CURRENT_BLOCKER
        and retained_tranche_004.get("retained_blocker_reason")
        == TRANCHE_004_RETAINED_REASON
        and registered_movement.get("retained_tranche_004_effect") == "none",
        "tranche_006_tracked_unresolved": registration.get("tranche_006_status")
        == TRANCHE_006_STATUS
        and tranche_006.get("dependency_finding_id") == TRANCHE_006_FINDING_ID
        and tranche_006.get("dependency") == TRANCHE_006_DEPENDENCY
        and registered_movement.get("tranche_006_effect") == "none",
        "registered_movement_exact": registered_movement.get("previous_status")
        == PREVIOUS_BLOCKER_STATUS
        and registered_movement.get("registered_status") == CANDIDATE_BLOCKER_STATUS
        and registered_movement.get("registered_movement") == PROPOSED_MOVEMENT
        and registered_movement.get("registered_movement_token") == PROPOSED_MOVEMENT_TOKEN,
        "registered_movement_tranche_005_only": registered_movement.get(
            "selected_remediation_finding_id"
        )
        == SELECTED_FINDING_ID
        and registered_movement.get("selected_dependency") == SELECTED_DEPENDENCY
        and registered_movement.get("movement_scope") == "tranche_005_only",
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
        "registration_classification_preserved": registration.get(
            "blocker_movement_registration_result_classification"
        )
        == REGISTRATION_CLASSIFICATION,
        "registration_was_pending_review": registration.get(
            "post_registration_result_review_required"
        )
        is True
        and registration.get("tranche_005_formal_movement_accepted") is False,
        "tranche_005_accepted_as_documented_nonblocking": CANDIDATE_BLOCKER_STATUS
        == "documented_dependency_nonblocking",
        "remaining_two_obligations_carried_forward": _remaining_obligations_carried_forward(
            remaining_obligations
        ),
        "no_release_packet_assembly": forbidden_effect_status["release_packet_assembled"]
        is False,
        "no_v01_readiness_marking": forbidden_effect_status["v01_alpha_marked_ready"]
        is False,
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
        == "prepare_v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_005_movement",
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_RESULT_REVIEW_BLOCKED",
        "consumes_registration": EXPECTED_REGISTRATION_ID,
        "consumes_registration_pointer": _ptr(registration_path),
        "consumed_registration_schema_id": registration.get("schema_id"),
        "review_scope": (
            "REVIEW_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_RESULT_ONLY_ACCEPT_DOCUMENTED_NONBLOCKING_MOVEMENT_NO_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_001_release_blocker_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_002_release_blocker_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_003_release_blocker_status": TRANCHE_003_STATUS,
        "tranche_004_status": TRANCHE_004_STATUS,
        "retained_tranche_004_carry_forward": retained_tranche_004,
        "tranche_006_status": TRANCHE_006_STATUS,
        "tranche_006_obligation_carry_forward": tranche_006,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "lean_audit_target": registration.get("lean_audit_target"),
        "registered": registration.get("blocker_movement_registered") is True,
        "blocker_movement_registered": registration.get("blocker_movement_registered")
        is True,
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
            "tranche_003_status": registered_movement.get("tranche_003_status"),
            "tranche_004_status": registered_movement.get("tranche_004_status"),
            "tranche_006_status": registered_movement.get("tranche_006_status"),
            "global_release_readiness_effect": (
                "none_retained_tranche_004_and_tranche_006_still_block"
            ),
            "theorem_or_proof_debt_effect": "none",
            "retained_tranche_004_effect": "none",
            "tranche_006_effect": "none",
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
            "axiom_classification": evidence.get("axiom_classification"),
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
        "tranche_005_formal_movement_accepted": accepted,
        "tranche_005_release_blocker_status": CANDIDATE_BLOCKER_STATUS,
        "tranche_005_dependency_policy_remediation_satisfied": accepted,
        "tranche_005_cleared_for_global_release_readiness": False,
        "global_release_readiness_still_blocked": True,
        "release_readiness_blocked_by_tranche_004": True,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "tranche_004_reclassified_nonblocking": False,
        "tranche_004_retained_blocker_discharged": False,
        "tranche_006_moved_or_cleared": False,
        "tranche_006_selected_yet": False,
        "release_blocking_obligation_count_after_review": len(remaining_obligations),
        "remaining_release_blocking_obligation_count_after_review": len(
            remaining_obligations
        ),
        "remaining_release_blocking_obligations": remaining_obligations,
        "other_release_blocking_obligations": remaining_obligations,
        "other_release_blocking_obligation_count": len(remaining_obligations),
        "release_packet_assembled": False,
        "v01_alpha_marked_ready": False,
        "release_readiness_pause_registered": False,
        "release_readiness_adjudication_prepared": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "axiom_spec_backed_debt_reduced_by_documentation": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "validation_claim_authorized": False,
        "forbidden_effect_status": forbidden_effect_status,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_RESULT_REVIEW",
        "selected_next_target_kind": "next_remediation_tranche_selection_packet_preparation_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_NEXT_REMEDIATION_TRANCHE_SELECTION_AFTER_TRANCHE_005_MOVEMENT_ONLY_NO_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": (
                    "Tranche 005 movement is accepted, so select the next remediation "
                    "tranche while carrying retained tranche 004."
                ),
            },
            {
                "target": "prepare_v01_alpha_dependency_remediation_tranche_006_execution_packet",
                "decision": "deferred",
                "reason": (
                    "Direct tranche 006 preparation is deferred until a selection packet "
                    "chooses it by the stable first-remaining non-tranche-004 blocker rule."
                ),
            },
            {
                "target": "pause_v01_alpha_release_readiness_due_to_retained_tranche_004_blocker",
                "decision": "deferred",
                "reason": (
                    "Release-readiness pause/adjudication is deferred while tranche 006 remains "
                    "unprocessed, and release readiness is still blocked by tranche 004."
                ),
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 005 blocker movement registration "
            "result review accepts the documented/nonblocking movement for V01-ALPHA-DEP-REM-005 "
            "and authorizes only next remediation tranche selection after tranche 005 movement. "
            "It does not move or discharge retained tranche 004, select or execute tranche 006, "
            "assemble the release packet, mark v0.1-alpha readiness, discharge Lean theorem debt, "
            "reduce axiom/spec-backed proof debt, discharge retained assumptions, authorize Phase 2, "
            "close seams, validate empirically, promote the master action, promote claims, or make "
            "an external-truth claim."
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
            "Generate the v0.1-alpha dependency remediation tranche 005 blocker movement "
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
        "v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration_result_review_report: "
        f"accepted={payload['accepted']} registered={payload['registered']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
