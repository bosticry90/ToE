from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_STATUS_ADJUDICATION_PACKET_20260515_v0"
PACKET_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_STATUS_ADJUDICATION_PACKET_v0"
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_STATUS_ADJUDICATION_PACKET_PREPARED_"
    "WITH_NO_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_DOCUMENTATION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_STATUS_ADJUDICATION_PACKET_20260515_v0.json"
)

EXPECTED_RESULT_REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_DOCUMENTATION_PACKET_RESULT_REVIEW_v0"
)
EXPECTED_RESULT_REVIEW_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_DOCUMENTATION_PACKET_RESULT_REVIEW_"
    "ACCEPTS_DOCUMENTATION_AND_AUTHORIZES_STATUS_ADJUDICATION_PACKET_PREPARATION_ONLY"
)
EXPECTED_RESULT_REVIEW_SELECTED_TARGET = (
    "prepare_v01_alpha_dependency_remediation_tranche_002_status_adjudication_packet"
)
TRANCHE_001_STATUS = "documented_dependency_nonblocking"
SELECTED_REMEDIATION_FINDING_ID = "V01-ALPHA-DEP-REM-002"
SELECTED_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-002"
SELECTED_DEPENDENCY = "stationary_implies_operator_zero"
SELECTED_DEPENDENCY_CLASS = "lean_theorem_dependency"
LEAN_TARGET = "ToeFormal.QFT.FreeScalarDerivation.stationary_implies_operator_zero"
EXPECTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
POLICY_CLASSIFICATION = "policy_acceptable_with_documentation_requirement"
DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION = (
    "documentation_accepted_pending_tranche_002_status_adjudication"
)
NEXT_TARGET = "review_v01_alpha_dependency_remediation_tranche_002_status_adjudication_packet_result"

RELEASE_BLOCKER_IDS = [
    "V01-ALPHA-DEP-REM-002",
    "V01-ALPHA-DEP-REM-003",
    "V01-ALPHA-DEP-REM-004",
    "V01-ALPHA-DEP-REM-005",
    "V01-ALPHA-DEP-REM-006",
]

OTHER_BLOCKER_IDS = [
    "V01-ALPHA-DEP-REM-003",
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


def _accepted_evidence(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("accepted_lean_dependency_evidence", {}))


def _release_blockers(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("release_blocking_obligations_carry_forward", []))


def _other_obligations(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("other_release_blocking_obligations", []))


def _release_blockers_tracked(rows: list[dict[str, Any]]) -> bool:
    return len(rows) == 5 and [
        row.get("dependency_finding_id") for row in rows
    ] == RELEASE_BLOCKER_IDS


def _other_obligations_carried_forward(rows: list[dict[str, Any]]) -> bool:
    return (
        len(rows) == 4
        and [row.get("dependency_finding_id") for row in rows] == OTHER_BLOCKER_IDS
        and all(row.get("modified_by_tranche_002") is False for row in rows)
        and all(
            row.get("status_carry_forward") == "tracked_unmodified_not_audited_in_tranche_002"
            for row in rows
        )
    )


def build_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    evidence = _accepted_evidence(result_review)
    release_blockers = _release_blockers(result_review)
    other_obligations = _other_obligations(result_review)
    documentation_surface = dict(result_review.get("documentation_surface", {}))
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_documentation_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "documentation_result_review_accepted": result_review.get("accepted") is True,
        "documentation_result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "documentation_result_review_selected_this_packet": result_review.get(
            "selected_next_target"
        )
        == EXPECTED_RESULT_REVIEW_SELECTED_TARGET,
        "status_adjudication_packet_preparation_authorized": result_review.get(
            "status_adjudication_packet_preparation_authorized"
        )
        is True,
        "previous_result_review_did_not_prepare_or_execute_status_adjudication": result_review.get(
            "status_adjudication_packet_prepared"
        )
        is False
        and result_review.get("status_adjudication_executed") is False,
        "selected_tranche_expected": result_review.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID,
        "selected_finding_expected": result_review.get("selected_remediation_finding_id")
        == SELECTED_REMEDIATION_FINDING_ID,
        "selected_dependency_expected": result_review.get("selected_dependency")
        == SELECTED_DEPENDENCY,
        "selected_dependency_class_expected": result_review.get("selected_dependency_class")
        == SELECTED_DEPENDENCY_CLASS,
        "lean_audit_target_preserved": result_review.get("lean_audit_target", {}).get(
            "lean_target"
        )
        == LEAN_TARGET,
        "tranche_001_documented_nonblocking_preserved": result_review.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS,
        "exact_lean_dependency_evidence_preserved": evidence.get("parsed_axioms")
        == EXPECTED_AXIOMS
        and evidence.get("exact_axioms_or_dependencies_used") == EXPECTED_AXIOMS
        and evidence.get("standard_lean_axioms_used") == EXPECTED_AXIOMS,
        "project_axioms_used_empty": evidence.get("project_axioms_used") == []
        and evidence.get("project_axiom_count") == 0,
        "policy_classification_preserved": result_review.get("policy_classification")
        == POLICY_CLASSIFICATION,
        "documentation_result_review_classification_preserved": result_review.get(
            "documentation_result_review_classification"
        )
        == DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION,
        "documentation_accepted_as_documentation_only": result_review.get(
            "documentation_accepted_only_as_documentation"
        )
        is True
        and documentation_surface.get("exists") is True
        and documentation_surface.get("accepted_as_documentation") is True,
        "tranche_002_not_cleared": result_review.get("remediation_fully_satisfied") is False
        and result_review.get("blocker_movement_authorized") is False
        and result_review.get("blocker_movement_registered") is False
        and result_review.get("tranche_002_release_blocker_status")
        == "still_blocking_pending_status_adjudication_packet",
        "release_blockers_remain_tracked": _release_blockers_tracked(release_blockers),
        "other_four_obligations_carried_forward": _other_obligations_carried_forward(
            other_obligations
        ),
        "prepares_status_adjudication_only": forbidden_effect_status[
            "status_adjudication_executed"
        ]
        is False
        and forbidden_effect_status["status_decision_made"] is False,
        "does_not_clear_or_move_blocker": forbidden_effect_status[
            "blocker_fully_remediated"
        ]
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
        == "review_v01_alpha_dependency_remediation_tranche_002_status_adjudication_packet_result",
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_STATUS_ADJUDICATION_PACKET_BLOCKED",
        "consumes_documentation_packet_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_documentation_packet_result_review_pointer": _ptr(result_review_path),
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "packet_scope": (
            "PREPARE_TRANCHE_002_STATUS_ADJUDICATION_PACKET_ONLY_NO_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_REMEDIATION_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "lean_audit_target": result_review.get("lean_audit_target"),
        "accepted_lean_dependency_evidence": {
            "parsed_axioms": evidence.get("parsed_axioms"),
            "exact_axioms_or_dependencies_used": evidence.get(
                "exact_axioms_or_dependencies_used"
            ),
            "standard_lean_axioms_used": evidence.get("standard_lean_axioms_used"),
            "standard_lean_axiom_count": evidence.get("standard_lean_axiom_count"),
            "project_axioms_used": evidence.get("project_axioms_used"),
            "project_axiom_count": evidence.get("project_axiom_count"),
            "classification": evidence.get("classification"),
            "raw_output": evidence.get("raw_output"),
        },
        "policy_classification": POLICY_CLASSIFICATION,
        "documentation_result_review_classification": DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION,
        "documentation_surface": documentation_surface,
        "documentation_accepted_only_as_documentation": True,
        "status_adjudication_question": (
            "Given accepted Lean dependency evidence, no project axioms, accepted "
            "release-policy posture, and accepted documentation, can tranche 002 move "
            "from release-blocking to a documented/narrower dependency status?"
        ),
        "status_adjudication_inputs": [
            "accepted Lean dependency evidence [propext, Classical.choice, Quot.sound]",
            "project_axioms_used = []",
            "policy_acceptable_with_documentation_requirement",
            "documentation accepted as documentation only",
            "tranche 001 status = documented_dependency_nonblocking",
            "remaining release-blocking obligations tracked and unchanged",
        ],
        "candidate_status_outcomes": [
            "remediation_satisfied_for_dependency_policy_only",
            "documentation_accepted_but_recheck_required",
            "retained_blocker_pending_additional_evidence",
            "status_adjudication_failed_requires_redesign",
        ],
        "status_adjudication_acceptance_criteria": [
            "The exact Lean dependency evidence remains unchanged.",
            "project_axioms_used remains empty.",
            "The release-policy classification remains policy_acceptable_with_documentation_requirement.",
            "The documentation surface remains accepted only as documentation.",
            "Tranche 001 remains documented_dependency_nonblocking.",
            "The status decision does not imply global theorem/proof debt discharge or release readiness.",
        ],
        "status_adjudication_failure_criteria": [
            "The evidence changes or includes project-local axioms.",
            "The documentation is treated as a proof or theorem-debt discharge.",
            "The status adjudication attempts to assemble the release or mark readiness.",
            "The status adjudication modifies any remaining blocker outside tranche 002.",
        ],
        "status_adjudication_packet_prepared": accepted,
        "status_adjudication_executed": False,
        "status_decision_made": False,
        "blocker_status_adjudicated": False,
        "tranche_002_release_blocker_status": (
            "still_blocking_pending_status_adjudication_packet_result_review"
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_STATUS_ADJUDICATION_PACKET",
        "selected_next_target_kind": "status_adjudication_packet_result_review_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_TRANCHE_002_STATUS_ADJUDICATION_PACKET_RESULT_ONLY_NO_STATUS_DECISION_OR_BLOCKER_MOVEMENT"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The tranche 002 status adjudication packet must be reviewed before the status question can be executed.",
            },
            {
                "target": "execute_v01_alpha_dependency_remediation_tranche_002_status_adjudication",
                "decision": "deferred",
                "reason": "Status adjudication execution requires acceptance of this preparation packet.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Release-readiness adjudication remains blocked by tranche 002 status adjudication and tracked blockers.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 002 status adjudication packet "
            "prepares the narrow status question only. It does not execute status adjudication, "
            "clear or move tranche 002, assemble the release packet, mark v0.1-alpha readiness, "
            "discharge Lean theorem debt, reduce axiom/spec-backed proof debt, discharge retained "
            "assumptions, authorize Phase 2, close seams, validate empirically, promote the master "
            "action, promote claims, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_packet(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha dependency remediation tranche 002 status adjudication packet."
        )
    )
    parser.add_argument("--result-review", type=Path, default=DEFAULT_RESULT_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    result_review_path = (
        ns.result_review if ns.result_review.is_absolute() else (REPO_ROOT / ns.result_review)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_dependency_remediation_tranche_002_status_adjudication_packet_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
