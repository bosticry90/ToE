from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_STATUS_ADJUDICATION_PACKET_RESULT_REVIEW_20260515_v0"
)
REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_STATUS_ADJUDICATION_PACKET_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_STATUS_ADJUDICATION_PACKET_RESULT_REVIEW_"
    "ACCEPTS_STATUS_QUESTION_PREPARATION_AND_AUTHORIZES_STATUS_ADJUDICATION_EXECUTION_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_STATUS_ADJUDICATION_PACKET_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_STATUS_ADJUDICATION_PACKET_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_PACKET_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_STATUS_ADJUDICATION_PACKET_v0"
EXPECTED_PACKET_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_STATUS_ADJUDICATION_PACKET_PREPARED_"
    "WITH_NO_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
)
EXPECTED_PACKET_SELECTED_TARGET = (
    "review_v01_alpha_dependency_remediation_tranche_003_status_adjudication_packet_result"
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
RESULT_REVIEW_CLASSIFICATION = "status_question_preparation_accepted_pending_status_execution"
NEXT_TARGET = "execute_v01_alpha_dependency_remediation_tranche_003_status_adjudication"

RELEASE_BLOCKER_IDS = [
    "V01-ALPHA-DEP-REM-003",
    "V01-ALPHA-DEP-REM-004",
    "V01-ALPHA-DEP-REM-005",
    "V01-ALPHA-DEP-REM-006",
]

OTHER_BLOCKER_IDS = [
    "V01-ALPHA-DEP-REM-004",
    "V01-ALPHA-DEP-REM-005",
    "V01-ALPHA-DEP-REM-006",
]

FORBIDDEN_EFFECTS = [
    "status_adjudication_executed",
    "status_decision_made",
    "blocker_status_adjudicated",
    "blocker_fully_remediated",
    "blocker_movement_authorized",
    "blocker_movement_registered",
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


def _accepted_evidence(packet: dict[str, Any]) -> dict[str, Any]:
    return dict(packet.get("accepted_lean_dependency_evidence", {}))


def _documentation_surface(packet: dict[str, Any]) -> dict[str, Any]:
    return dict(packet.get("documentation_surface", {}))


def _release_blockers(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return list(packet.get("release_blocking_obligations_carry_forward", []))


def _other_obligations(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return list(packet.get("other_release_blocking_obligations", []))


def _release_blockers_tracked(rows: list[dict[str, Any]]) -> bool:
    return (
        len(rows) == 4
        and [row.get("dependency_finding_id") for row in rows] == RELEASE_BLOCKER_IDS
        and all(row.get("remediation_execution_status") == "not_executed_v0" for row in rows)
    )


def _other_obligations_carried_forward(rows: list[dict[str, Any]]) -> bool:
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
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    evidence = _accepted_evidence(packet)
    documentation_surface = _documentation_surface(packet)
    release_blockers = _release_blockers(packet)
    other_obligations = _other_obligations(packet)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    expected_inputs = [
        "accepted Lean dependency evidence [propext, Classical.choice, Quot.sound]",
        "project_axioms_used = []",
        "policy_acceptable_with_documentation_requirement",
        "documentation accepted as documentation only",
        "tranche 001 status = documented_dependency_nonblocking",
        "tranche 002 status = documented_dependency_nonblocking",
        "remaining release-blocking obligations tracked and unchanged",
    ]
    expected_candidate_status_outcomes = [
        "documented_dependency_nonblocking_pending_result_review",
        "documentation_accepted_but_recheck_required",
        "retained_blocker_pending_additional_evidence",
        "status_adjudication_failed_requires_redesign",
    ]

    acceptance_criteria = {
        "consumes_expected_packet": packet.get("packet_id") == EXPECTED_PACKET_ID,
        "packet_accepted": packet.get("accepted") is True,
        "packet_outcome_expected": packet.get("outcome_id") == EXPECTED_PACKET_OUTCOME,
        "packet_selected_this_review": packet.get("selected_next_target")
        == EXPECTED_PACKET_SELECTED_TARGET,
        "selected_tranche_expected": packet.get("selected_tranche_id") == SELECTED_TRANCHE_ID,
        "selected_finding_expected": packet.get("selected_remediation_finding_id")
        == SELECTED_REMEDIATION_FINDING_ID,
        "selected_dependency_expected": packet.get("selected_dependency") == SELECTED_DEPENDENCY,
        "selected_dependency_class_expected": packet.get("selected_dependency_class")
        == SELECTED_DEPENDENCY_CLASS,
        "lean_audit_target_preserved": packet.get("lean_audit_target", {}).get("lean_target")
        == LEAN_TARGET,
        "tranche_001_documented_nonblocking_preserved": packet.get("tranche_001_status")
        == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": packet.get("tranche_002_status")
        == TRANCHE_002_STATUS,
        "exact_lean_dependency_evidence_preserved": evidence.get("parsed_axioms")
        == EXPECTED_AXIOMS
        and evidence.get("exact_axioms_or_dependencies_used") == EXPECTED_AXIOMS
        and evidence.get("standard_lean_axioms_used") == EXPECTED_AXIOMS,
        "project_axioms_used_empty": evidence.get("project_axioms_used")
        == PROJECT_AXIOMS_USED
        and evidence.get("project_axiom_count") == 0,
        "policy_classification_preserved": packet.get("policy_classification")
        == POLICY_CLASSIFICATION,
        "documentation_result_review_classification_preserved": packet.get(
            "documentation_result_review_classification"
        )
        == DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION,
        "documentation_accepted_as_documentation_only": packet.get(
            "documentation_accepted_only_as_documentation"
        )
        is True
        and documentation_surface.get("exists") is True
        and documentation_surface.get("accepted_as_documentation") is True,
        "status_question_prepared_only": packet.get("status_adjudication_packet_prepared")
        is True
        and packet.get("status_adjudication_executed") is False
        and packet.get("status_decision_made") is False
        and packet.get("blocker_status_adjudicated") is False,
        "status_question_records_required_inputs": packet.get("status_adjudication_inputs")
        == expected_inputs,
        "candidate_status_outcomes_defined": packet.get("candidate_status_outcomes")
        == expected_candidate_status_outcomes,
        "tranche_003_not_cleared_or_moved": packet.get("remediation_fully_satisfied")
        is False
        and packet.get("blocker_movement_authorized") is False
        and packet.get("blocker_movement_registered") is False
        and packet.get("tranche_003_release_blocker_status")
        == "still_blocking_pending_status_adjudication_packet_result_review",
        "release_blockers_remain_tracked": _release_blockers_tracked(release_blockers),
        "other_three_obligations_carried_forward": _other_obligations_carried_forward(
            other_obligations
        ),
        "no_status_adjudication_execution_during_review": forbidden_effect_status[
            "status_adjudication_executed"
        ]
        is False
        and forbidden_effect_status["status_decision_made"] is False,
        "does_not_move_blocker": forbidden_effect_status["blocker_fully_remediated"]
        is False
        and forbidden_effect_status["blocker_movement_authorized"] is False
        and forbidden_effect_status["blocker_movement_registered"] is False
        and forbidden_effect_status["blocker_status_adjudicated"] is False,
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
        == "execute_v01_alpha_dependency_remediation_tranche_003_status_adjudication",
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_STATUS_ADJUDICATION_PACKET_RESULT_REVIEW_BLOCKED",
        "consumes_packet": EXPECTED_PACKET_ID,
        "consumes_packet_pointer": _ptr(packet_path),
        "consumed_packet_schema_id": packet.get("schema_id"),
        "review_scope": (
            "REVIEW_TRANCHE_003_STATUS_ADJUDICATION_PACKET_RESULT_ONLY_"
            "AUTHORIZE_STATUS_ADJUDICATION_EXECUTION_NO_STATUS_DECISION_OR_BLOCKER_MOVEMENT"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_REMEDIATION_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "lean_audit_target": packet.get("lean_audit_target"),
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
        "status_adjudication_question": packet.get("status_adjudication_question"),
        "status_adjudication_inputs": packet.get("status_adjudication_inputs"),
        "candidate_status_outcomes": packet.get("candidate_status_outcomes"),
        "status_adjudication_acceptance_criteria": packet.get(
            "status_adjudication_acceptance_criteria"
        ),
        "status_adjudication_failure_criteria": packet.get(
            "status_adjudication_failure_criteria"
        ),
        "status_adjudication_packet_result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "status_adjudication_execution_authorized": accepted,
        "status_adjudication_executed": False,
        "status_decision_made": False,
        "blocker_status_adjudicated": False,
        "target_status_candidate": "documented_dependency_nonblocking_pending_result_review",
        "tranche_003_release_blocker_status": (
            "still_blocking_pending_status_adjudication_execution"
        ),
        "remediation_fully_satisfied": False,
        "blocker_movement_authorized": False,
        "blocker_movement_registered": False,
        "release_blocking_obligations_carry_forward": release_blockers,
        "release_blocking_obligation_count": len(release_blockers),
        "other_release_blocking_obligations": other_obligations,
        "other_release_blocking_obligation_count": len(other_obligations),
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_STATUS_ADJUDICATION_PACKET_RESULT_REVIEW",
        "selected_next_target_kind": "status_adjudication_execution_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "EXECUTE_TRANCHE_003_STATUS_ADJUDICATION_ONLY_NO_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The status question preparation is accepted, so the narrow tranche 003 status adjudication execution can proceed.",
            },
            {
                "target": "prepare_v01_alpha_dependency_remediation_tranche_003_blocker_movement_registration_packet",
                "decision": "deferred",
                "reason": "Blocker movement registration requires status adjudication execution and result review first.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Release-readiness adjudication remains blocked by tranche 003 status execution and tracked blockers.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 003 status adjudication packet result "
            "review accepts the prepared status question and authorizes only its bounded execution. "
            "It does not execute status adjudication, make the status decision, clear or move "
            "tranche 003, assemble the release packet, mark v0.1-alpha readiness, discharge Lean "
            "theorem debt, reduce axiom/spec-backed proof debt, discharge retained assumptions, "
            "authorize Phase 2, close seams, validate empirically, promote the master action, "
            "promote claims, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha dependency remediation tranche 003 status adjudication "
            "packet result review."
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
    payload = write_result_review(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_dependency_remediation_tranche_003_status_adjudication_packet_result_review_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
