from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_005_status_adjudication_packet_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION,
    EXPECTED_AXIOMS,
    LEAN_AUDIT_COMMAND,
    LEAN_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    POLICY_CLASSIFICATION,
    PROJECT_AXIOMS_USED,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SELECTED_DEPENDENCY,
    SELECTED_DEPENDENCY_CLASS,
    SELECTED_FINDING_ID,
    SELECTED_TRANCHE_ID,
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
SCHEMA_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_STATUS_ADJUDICATION_20260515_v0"
EXECUTION_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_STATUS_ADJUDICATION_v0"
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_STATUS_ADJUDICATED_PENDING_RESULT_REVIEW_"
    "WITH_NO_RELEASE_PROMOTION"
)

DEFAULT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_STATUS_ADJUDICATION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_STATUS_ADJUDICATION_20260515_v0.json"
)

EXPECTED_SELECTED_TARGET = "execute_v01_alpha_dependency_remediation_tranche_005_status_adjudication"
STATUS_DECISION = "documented_dependency_nonblocking_pending_result_review"
STATUS_CLASSIFICATION = "status_adjudicated_documented_dependency_pending_result_review"
NEXT_TARGET = "review_v01_alpha_dependency_remediation_tranche_005_status_adjudication_result"

FORBIDDEN_EFFECTS = [
    "blocker_fully_remediated",
    "blocker_movement_authorized",
    "blocker_movement_registered",
    "tranche_004_moved_to_documented_dependency_nonblocking",
    "tranche_004_reclassified_nonblocking",
    "tranche_004_retained_blocker_discharged",
    "remediation_closure_executed",
    "remediation_executed",
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


def _accepted_evidence(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("accepted_lean_dependency_evidence", {}))


def _documentation_surface(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("documentation_surface", {}))


def _retained_tranche_004(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("retained_tranche_004_carry_forward", {}))


def _tranche_006(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("tranche_006_obligation_carry_forward", {}))


def _release_blockers(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("release_blocking_obligations_carry_forward", []))


def _other_obligations(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("other_release_blocking_obligations", []))


def _release_blockers_tracked(rows: list[dict[str, Any]]) -> bool:
    return (
        len(rows) == 3
        and [row.get("dependency_finding_id") for row in rows]
        == [TRANCHE_004_FINDING_ID, SELECTED_FINDING_ID, TRANCHE_006_FINDING_ID]
        and rows[0].get("status_carry_forward") == TRANCHE_004_STATUS
        and rows[1].get("status_carry_forward")
        == "pending_result_review_policy_acceptable_with_documentation_requirement"
        and rows[2].get("status_carry_forward") == TRANCHE_006_STATUS
    )


def _other_obligations_carried_forward(rows: list[dict[str, Any]]) -> bool:
    return (
        len(rows) == 2
        and [row.get("dependency_finding_id") for row in rows]
        == [TRANCHE_004_FINDING_ID, TRANCHE_006_FINDING_ID]
        and all(
            row.get("modified_by_tranche_005_policy_adjudication") is False
            for row in rows
        )
    )


def build_adjudication(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    evidence = _accepted_evidence(result_review)
    documentation_surface = _documentation_surface(result_review)
    retained_tranche_004 = _retained_tranche_004(result_review)
    tranche_006 = _tranche_006(result_review)
    release_blockers = _release_blockers(result_review)
    other_obligations = _other_obligations(result_review)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    status_decision = {
        "question": result_review.get("status_adjudication_question"),
        "decision": STATUS_DECISION,
        "classification": STATUS_CLASSIFICATION,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "basis": [
            "accepted Lean dependency evidence [propext, Classical.choice, Quot.sound]",
            "project_axioms_used = []",
            "policy_acceptable_with_documentation_requirement",
            "documentation accepted as documentation only",
            "tranche 001 status = documented_dependency_nonblocking",
            "tranche 002 status = documented_dependency_nonblocking",
            "tranche 003 status = documented_dependency_nonblocking",
            "tranche 004 status = retained_release_blocking_source_map_blocker",
            "tranche 006 status = tracked_unresolved",
        ],
        "meaning": (
            "Tranche 005 has enough dependency-policy evidence to be treated as a documented "
            "dependency nonblocking status candidate, pending result review."
        ),
        "does_not_clear_blocker_by_itself": True,
        "does_not_register_blocker_movement": True,
        "does_not_move_retained_tranche_004": True,
        "does_not_discharge_theorem_or_proof_debt": True,
        "does_not_mark_release_readiness": True,
        "formal_blocker_movement_requires_result_review": True,
    }

    acceptance_criteria = {
        "consumes_expected_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_accepted": result_review.get("accepted") is True,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_authorized_this_execution": result_review.get("selected_next_target")
        == EXPECTED_SELECTED_TARGET,
        "status_adjudication_execution_authorized": result_review.get(
            "status_adjudication_execution_authorized"
        )
        is True,
        "selected_tranche_expected": result_review.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID,
        "selected_finding_expected": result_review.get("selected_remediation_finding_id")
        == SELECTED_FINDING_ID,
        "selected_dependency_expected": result_review.get("selected_dependency")
        == SELECTED_DEPENDENCY,
        "selected_dependency_class_expected": result_review.get("selected_dependency_class")
        == SELECTED_DEPENDENCY_CLASS,
        "lean_audit_target_preserved": result_review.get("lean_audit_target", {}).get(
            "lean_target"
        )
        == LEAN_TARGET
        and result_review.get("lean_audit_target", {}).get("command") == LEAN_AUDIT_COMMAND,
        "tranche_001_documented_nonblocking_preserved": result_review.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": result_review.get(
            "tranche_002_status"
        )
        == TRANCHE_002_STATUS,
        "tranche_003_documented_nonblocking_preserved": result_review.get(
            "tranche_003_status"
        )
        == TRANCHE_003_STATUS,
        "tranche_004_retained_blocker_preserved": result_review.get("tranche_004_status")
        == TRANCHE_004_STATUS
        and retained_tranche_004.get("status") == TRANCHE_004_STATUS
        and retained_tranche_004.get("dependency") == TRANCHE_004_DEPENDENCY
        and retained_tranche_004.get("current_blocker") == TRANCHE_004_CURRENT_BLOCKER
        and retained_tranche_004.get("retained_blocker_reason")
        == TRANCHE_004_RETAINED_REASON,
        "tranche_006_tracked_unresolved": result_review.get("tranche_006_status")
        == TRANCHE_006_STATUS
        and tranche_006.get("dependency") == TRANCHE_006_DEPENDENCY,
        "adjudicates_only_tranche_005": status_decision["selected_tranche_id"]
        == SELECTED_TRANCHE_ID
        and status_decision["selected_remediation_finding_id"] == SELECTED_FINDING_ID
        and status_decision["selected_dependency"] == SELECTED_DEPENDENCY,
        "accepted_lean_dependency_evidence_preserved_exactly": evidence.get("parsed_axioms")
        == EXPECTED_AXIOMS
        and evidence.get("exact_axioms_or_dependencies_used") == EXPECTED_AXIOMS
        and evidence.get("standard_lean_axioms_used") == EXPECTED_AXIOMS,
        "project_axioms_used_empty": evidence.get("project_axioms_used")
        == PROJECT_AXIOMS_USED
        and evidence.get("project_axiom_count") == 0,
        "policy_classification_preserved": result_review.get("policy_classification")
        == POLICY_CLASSIFICATION,
        "documentation_chain_preserved": result_review.get(
            "documentation_result_review_classification"
        )
        == DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION
        and result_review.get("documentation_accepted_only_as_documentation") is True
        and documentation_surface.get("exists") is True
        and documentation_surface.get("accepted_as_documentation") is True,
        "status_decision_is_allowed": STATUS_DECISION
        in [
            "documented_dependency_nonblocking_pending_result_review",
            "release_blocking_pending_additional_remediation",
            "documentation_accepted_but_recheck_required",
            "status_adjudication_failed_requires_redesign",
        ],
        "result_review_required_before_blocker_movement": status_decision[
            "formal_blocker_movement_requires_result_review"
        ]
        is True,
        "release_blockers_remain_tracked": _release_blockers_tracked(release_blockers),
        "other_obligations_carried_forward": _other_obligations_carried_forward(
            other_obligations
        ),
        "does_not_clear_or_move_blocker": forbidden_effect_status[
            "blocker_fully_remediated"
        ]
        is False
        and forbidden_effect_status["blocker_movement_authorized"] is False
        and forbidden_effect_status["blocker_movement_registered"] is False,
        "does_not_move_tranche_004": forbidden_effect_status[
            "tranche_004_moved_to_documented_dependency_nonblocking"
        ]
        is False
        and forbidden_effect_status["tranche_004_retained_blocker_discharged"] is False,
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
        == "review_v01_alpha_dependency_remediation_tranche_005_status_adjudication_result",
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "execution_id": EXECUTION_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "executed": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_STATUS_ADJUDICATION_BLOCKED",
        "consumes_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_result_review_pointer": _ptr(result_review_path),
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "execution_scope": (
            "EXECUTE_TRANCHE_005_STATUS_ADJUDICATION_ONLY_NO_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_004_status": TRANCHE_004_STATUS,
        "retained_tranche_004_carry_forward": retained_tranche_004,
        "tranche_006_status": TRANCHE_006_STATUS,
        "tranche_006_obligation_carry_forward": tranche_006,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "lean_audit_target": result_review.get("lean_audit_target"),
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
        "status_adjudication_executed": accepted,
        "status_decision_made": accepted,
        "status_adjudication_decision": status_decision,
        "status_adjudication_classification": STATUS_CLASSIFICATION,
        "tranche_005_status_candidate": STATUS_DECISION,
        "post_adjudication_result_review_required": True,
        "tranche_005_release_blocker_status": (
            "pending_result_review_documented_dependency_nonblocking_candidate"
        ),
        "global_release_readiness_still_blocked": True,
        "release_readiness_blocked_by_tranche_004": True,
        "remediation_closure_authorized": False,
        "remediation_fully_satisfied": False,
        "blocker_movement_authorized": False,
        "blocker_movement_registered": False,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "tranche_004_reclassified_nonblocking": False,
        "tranche_004_retained_blocker_discharged": False,
        "release_blocking_obligations_carry_forward": release_blockers,
        "release_blocking_obligation_count": len(release_blockers),
        "other_release_blocking_obligations": other_obligations,
        "other_release_blocking_obligation_count": len(other_obligations),
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_STATUS_ADJUDICATION",
        "selected_next_target_kind": "status_adjudication_result_review_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_TRANCHE_005_STATUS_ADJUDICATION_RESULT_ONLY_NO_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": (
                    "The status adjudication execution must be reviewed before any tranche 005 "
                    "blocker movement is recognized."
                ),
            },
            {
                "target": (
                    "prepare_v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration_packet"
                ),
                "decision": "deferred",
                "reason": (
                    "Blocker movement registration requires acceptance of the tranche 005 "
                    "status adjudication result."
                ),
            },
            {
                "target": "pause_v01_alpha_release_readiness_due_to_retained_tranche_004_blocker",
                "decision": "deferred",
                "reason": (
                    "Release-readiness adjudication remains blocked by retained tranche 004 and "
                    "tracked tranche 006."
                ),
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 005 status adjudication decides only "
            "that the selected dependency can be treated as a documented dependency nonblocking "
            "status candidate pending result review. It does not clear or move the blocker by "
            "itself, register blocker movement, move retained tranche 004, assemble the release "
            "packet, mark v0.1-alpha readiness, discharge Lean theorem debt, reduce "
            "axiom/spec-backed proof debt, discharge retained assumptions, authorize Phase 2, "
            "close seams, validate empirically, promote the master action, promote claims, or "
            "make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_adjudication(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_adjudication(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha dependency remediation tranche 005 status adjudication."
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
    payload = write_adjudication(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_dependency_remediation_tranche_005_status_adjudication_report: "
        f"accepted={payload['accepted']} classification={payload['status_adjudication_classification']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
