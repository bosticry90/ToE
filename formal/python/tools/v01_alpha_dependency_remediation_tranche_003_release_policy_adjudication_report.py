from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_RELEASE_POLICY_ADJUDICATION_20260515_v0"
)
EXECUTION_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_RELEASE_POLICY_ADJUDICATION_v0"
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_RELEASE_POLICY_ADJUDICATED_"
    "WITH_NO_RELEASE_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_RELEASE_POLICY_ADJUDICATION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_RELEASE_POLICY_ADJUDICATION_20260515_v0.json"
)

EXPECTED_RESULT_REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_RELEASE_POLICY_ADJUDICATION_PACKET_RESULT_REVIEW_v0"
)
EXPECTED_RESULT_REVIEW_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_RELEASE_POLICY_ADJUDICATION_PACKET_RESULT_REVIEW_"
    "ACCEPTS_POLICY_QUESTION_PREPARATION_AND_AUTHORIZES_POLICY_ADJUDICATION_EXECUTION_ONLY"
)
EXPECTED_SELECTED_TARGET = (
    "execute_v01_alpha_dependency_remediation_tranche_003_release_policy_adjudication"
)
TRANCHE_001_STATUS = "documented_dependency_nonblocking"
TRANCHE_002_STATUS = "documented_dependency_nonblocking"
SELECTED_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-003"
SELECTED_FINDING_ID = "V01-ALPHA-DEP-REM-003"
SELECTED_DEPENDENCY = "finite_transport_theorems_construct_residual_package_v0"
SELECTED_DEPENDENCY_CLASS = "lean_bridge_dependency"
LEAN_TARGET = (
    "ToeFormal.Bridges.QMSTATTransportResidualPackage."
    "finite_transport_theorems_construct_residual_package_v0"
)
EXPECTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
PROJECT_AXIOMS_USED: list[str] = []
POLICY_QUESTION = (
    "Are [propext, Classical.choice, Quot.sound] acceptable standard Lean dependencies "
    "for tranche 003 / finite_transport_theorems_construct_residual_package_v0 under the "
    "v0.1-alpha release dependency policy, given project_axioms_used = []?"
)
POLICY_CLASSIFICATION = "policy_acceptable_with_documentation_requirement"
NEXT_TARGET = (
    "review_v01_alpha_dependency_remediation_tranche_003_release_policy_adjudication_result"
)

FORBIDDEN_EFFECTS = [
    "remediation_closure_executed",
    "broader_remediation_executed",
    "documentation_prepared",
    "expert_re_review_executed",
    "blocker_fully_remediated",
    "blocker_movement_authorized",
    "blocker_movement_registered",
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


def _other_blockers(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("other_release_blocking_obligations", []))


def _selected_obligation(rows: list[dict[str, Any]]) -> dict[str, Any]:
    for row in rows:
        if row.get("dependency_finding_id") == SELECTED_FINDING_ID:
            return dict(row)
    return {}


def _release_blockers_tracked(rows: list[dict[str, Any]]) -> bool:
    return (
        len(rows) == 4
        and [row.get("dependency_finding_id") for row in rows]
        == [
            "V01-ALPHA-DEP-REM-003",
            "V01-ALPHA-DEP-REM-004",
            "V01-ALPHA-DEP-REM-005",
            "V01-ALPHA-DEP-REM-006",
        ]
        and all(row.get("remediation_execution_status") == "not_executed_v0" for row in rows)
    )


def _other_blockers_unmodified(rows: list[dict[str, Any]]) -> bool:
    return (
        len(rows) == 3
        and all(row.get("modified_by_tranche_003") is False for row in rows)
        and all(
            row.get("status_carry_forward") == "tracked_unmodified_not_audited_in_tranche_003"
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
    release_blockers = _release_blockers(result_review)
    other_blockers = _other_blockers(result_review)
    selected_obligation = _selected_obligation(release_blockers)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    policy_decision = {
        "question": POLICY_QUESTION,
        "classification": POLICY_CLASSIFICATION,
        "standard_lean_axioms_reviewed": EXPECTED_AXIOMS,
        "project_axioms_used": evidence.get("project_axioms_used"),
        "project_axiom_count": evidence.get("project_axiom_count"),
        "decision": (
            "The standard Lean axioms propext, Classical.choice, and Quot.sound are "
            "acceptable for the v0.1-alpha dependency posture of "
            "finite_transport_theorems_construct_residual_package_v0 when no project-local "
            "axioms are used, provided the release materials document this standard-axiom "
            "posture."
        ),
        "decision_basis": [
            "Tranche 003 packet result review accepted the policy-question preparation.",
            "The selected dependency is finite_transport_theorems_construct_residual_package_v0.",
            "The accepted Lean dependency evidence is exactly [propext, Classical.choice, Quot.sound].",
            "project_axioms_used is exactly an empty list.",
            "The decision is specific to V01-ALPHA-DEP-REM-003 and is not inferred by analogy alone.",
        ],
        "documentation_requirement": (
            "A later documentation packet and result review must record that tranche 003 depends "
            "only on standard Lean axioms [propext, Classical.choice, Quot.sound] and no "
            "project-local axioms before blocker movement can be considered."
        ),
        "expert_re_review_required": False,
        "does_not_clear_blocker_by_itself": True,
        "does_not_discharge_theorem_or_proof_debt": True,
        "does_not_mark_release_readiness": True,
    }

    acceptance_criteria = {
        "consumes_expected_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_accepted": result_review.get("accepted") is True,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_authorized_this_execution": result_review.get("selected_next_target")
        == EXPECTED_SELECTED_TARGET,
        "policy_execution_authorized": result_review.get(
            "policy_adjudication_execution_authorized"
        )
        is True,
        "selected_tranche_expected": result_review.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID,
        "selected_finding_expected": result_review.get("selected_remediation_finding_id")
        == SELECTED_FINDING_ID,
        "selected_dependency_expected": result_review.get("selected_dependency")
        == SELECTED_DEPENDENCY
        and selected_obligation.get("dependency") == SELECTED_DEPENDENCY,
        "selected_dependency_class_expected": result_review.get("selected_dependency_class")
        == SELECTED_DEPENDENCY_CLASS
        and selected_obligation.get("dependency_class") == SELECTED_DEPENDENCY_CLASS,
        "tranche_001_documented_nonblocking_preserved": result_review.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": result_review.get(
            "tranche_002_status"
        )
        == TRANCHE_002_STATUS,
        "lean_audit_target_preserved": result_review.get("lean_audit_target", {}).get(
            "lean_target"
        )
        == LEAN_TARGET,
        "accepted_lean_dependency_evidence_preserved_exactly": evidence.get(
            "parsed_axioms"
        )
        == EXPECTED_AXIOMS
        and evidence.get("exact_axioms_or_dependencies_used") == EXPECTED_AXIOMS,
        "standard_lean_axioms_preserved": evidence.get("standard_lean_axioms_used")
        == EXPECTED_AXIOMS
        and evidence.get("standard_lean_axiom_count") == len(EXPECTED_AXIOMS),
        "project_axioms_used_empty": evidence.get("project_axioms_used")
        == PROJECT_AXIOMS_USED
        and evidence.get("project_axiom_count") == 0,
        "policy_question_matches_scope": result_review.get("policy_question")
        == POLICY_QUESTION,
        "adjudicates_only_tranche_003": policy_decision["classification"]
        == POLICY_CLASSIFICATION
        and result_review.get("selected_tranche_id") == SELECTED_TRANCHE_ID,
        "classification_is_allowed": POLICY_CLASSIFICATION
        in [
            "policy_acceptable_pending_result_review",
            "policy_acceptable_with_documentation_requirement",
            "policy_not_acceptable_requires_remediation_redesign",
            "policy_inconclusive_requires_expert_re_review",
        ],
        "decision_basis_is_tranche_003_specific": any(
            "not inferred by analogy alone" in basis
            for basis in policy_decision["decision_basis"]
        ),
        "documentation_requirement_recorded": bool(policy_decision["documentation_requirement"]),
        "release_blockers_remain_tracked": _release_blockers_tracked(release_blockers),
        "other_blockers_unmodified": _other_blockers_unmodified(other_blockers),
        "does_not_clear_or_move_blocker": forbidden_effect_status[
            "blocker_fully_remediated"
        ]
        is False
        and forbidden_effect_status["blocker_movement_authorized"] is False
        and forbidden_effect_status["blocker_movement_registered"] is False,
        "no_remediation_closure": forbidden_effect_status["remediation_closure_executed"]
        is False
        and forbidden_effect_status["broader_remediation_executed"] is False,
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
        == "review_v01_alpha_dependency_remediation_tranche_003_release_policy_adjudication_result",
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_RELEASE_POLICY_ADJUDICATION_BLOCKED",
        "consumes_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_result_review_pointer": _ptr(result_review_path),
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "execution_scope": (
            "EXECUTE_TRANCHE_003_RELEASE_POLICY_ADJUDICATION_ONLY_NO_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "selected_release_blocking_obligation": selected_obligation,
        "lean_audit_target": {
            "lean_target": result_review.get("lean_audit_target", {}).get("lean_target"),
            "command": result_review.get("lean_audit_target", {}).get("command"),
            "exit_code": result_review.get("lean_audit_target", {}).get("exit_code"),
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
        "policy_question": POLICY_QUESTION,
        "policy_classification": POLICY_CLASSIFICATION,
        "classification_options_considered": [
            "policy_acceptable_pending_result_review",
            "policy_acceptable_with_documentation_requirement",
            "policy_not_acceptable_requires_remediation_redesign",
            "policy_inconclusive_requires_expert_re_review",
        ],
        "policy_decision": policy_decision,
        "policy_adjudication_executed": accepted,
        "policy_decision_made": accepted,
        "release_policy_decision_made": accepted,
        "policy_acceptance_for_standard_lean_axioms": accepted,
        "documentation_requirement_open": True,
        "expert_re_review_required": False,
        "post_adjudication_result_review_required": True,
        "tranche_003_release_blocker_status": (
            "pending_result_review_policy_acceptable_with_documentation_requirement"
        ),
        "remediation_closure_authorized": False,
        "remediation_closure_executed": False,
        "remediation_fully_satisfied": False,
        "blocker_movement_authorized": False,
        "blocker_movement_registered": False,
        "release_blocking_obligations_carry_forward": release_blockers,
        "release_blocking_obligation_count": len(release_blockers),
        "other_release_blocking_obligations": other_blockers,
        "other_release_blocking_obligation_count": len(other_blockers),
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_RELEASE_POLICY_ADJUDICATION",
        "selected_next_target_kind": "release_policy_adjudication_result_review_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_TRANCHE_003_RELEASE_POLICY_ADJUDICATION_RESULT_ONLY_NO_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The policy adjudication result must be reviewed before documentation preparation or blocker status movement.",
            },
            {
                "target": "prepare_v01_alpha_dependency_remediation_tranche_003_documentation_packet",
                "decision": "deferred",
                "reason": "Documentation packet preparation requires policy-adjudication result review acceptance first.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Release-readiness adjudication remains blocked by the pending result review and tracked blockers.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 003 release-policy adjudication "
            "decides only that the standard Lean axioms [propext, Classical.choice, Quot.sound] "
            "are acceptable for finite_transport_theorems_construct_residual_package_v0 with a "
            "documentation requirement and no project-local axioms. It does not close "
            "remediation, move blockers, assemble the release packet, mark v0.1-alpha readiness, "
            "discharge theorem/proof debt, discharge retained assumptions, authorize Phase 2, "
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
            "Generate the v0.1-alpha dependency remediation tranche 003 release-policy adjudication."
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
        "v01_alpha_dependency_remediation_tranche_003_release_policy_adjudication_report: "
        f"accepted={payload['accepted']} classification={payload['policy_classification']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
