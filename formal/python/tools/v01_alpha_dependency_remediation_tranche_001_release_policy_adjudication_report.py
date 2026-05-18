from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_20260515_v0"
)
EXECUTION_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_v0"
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_RELEASE_POLICY_ADJUDICATED_"
    "WITH_NO_RELEASE_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_20260515_v0.json"
)

EXPECTED_RESULT_REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_PACKET_RESULT_REVIEW_v0"
)
EXPECTED_RESULT_REVIEW_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_PACKET_RESULT_REVIEW_"
    "ACCEPTS_POLICY_QUESTION_PREPARATION_AND_AUTHORIZES_POLICY_ADJUDICATION_EXECUTION_ONLY"
)
EXPECTED_SELECTED_TARGET = (
    "execute_v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication"
)
SELECTED_REMEDIATION_FINDING_ID = "V01-ALPHA-DEP-REM-001"
SELECTED_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-001"
SELECTED_DEPENDENCY = "master_action_stationary_implies_free_scalar_kg"
EXPECTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
POLICY_QUESTION = (
    "Are [propext, Classical.choice, Quot.sound] acceptable under the v0.1-alpha "
    "release policy for master_action_stationary_implies_free_scalar_kg, given that "
    "project_axioms_used is empty?"
)
POLICY_CLASSIFICATION = "policy_acceptable_with_documentation_requirement"
NEXT_TARGET = (
    "review_v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_result"
)

FORBIDDEN_EFFECTS = [
    "blocker_fully_remediated",
    "blocker_movement_authorized",
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


def _other_obligations(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("other_release_blocking_obligations", []))


def _other_obligations_carried_forward(result_review: dict[str, Any]) -> bool:
    rows = _other_obligations(result_review)
    return (
        len(rows) == 5
        and all(row.get("modified_by_tranche_001") is False for row in rows)
        and all(
            row.get("status_carry_forward") == "tracked_unmodified_not_executed_in_tranche_001"
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
    other_obligations = _other_obligations(result_review)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    policy_decision = {
        "question": POLICY_QUESTION,
        "classification": POLICY_CLASSIFICATION,
        "standard_lean_axioms_reviewed": EXPECTED_AXIOMS,
        "project_axioms_used": evidence.get("project_axioms_used"),
        "project_axiom_count": evidence.get("project_axiom_count"),
        "decision": (
            "The standard Lean axioms propext, Classical.choice, and Quot.sound are acceptable "
            "for the v0.1-alpha dependency posture of the selected theorem when no project-local "
            "axioms are used, provided the release materials document this standard-axiom posture."
        ),
        "documentation_requirement": (
            "A later result-review or release-policy follow-up must record that tranche 001 depends "
            "only on standard Lean axioms [propext, Classical.choice, Quot.sound] and no project-local "
            "axioms before the blocker can be downgraded."
        ),
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
        == SELECTED_REMEDIATION_FINDING_ID,
        "selected_dependency_expected": result_review.get("selected_dependency")
        == SELECTED_DEPENDENCY,
        "accepted_lean_dependency_evidence_preserved_exactly": evidence.get("parsed_axioms")
        == EXPECTED_AXIOMS,
        "project_axioms_used_empty": evidence.get("project_axioms_used") == []
        and evidence.get("project_axiom_count") == 0,
        "policy_question_matches_scope": result_review.get("policy_question") == POLICY_QUESTION,
        "adjudicates_only_tranche_001": policy_decision["classification"]
        == POLICY_CLASSIFICATION
        and result_review.get("selected_tranche_id") == SELECTED_TRANCHE_ID,
        "classification_is_allowed": POLICY_CLASSIFICATION
        in [
            "policy_acceptable_pending_result_review",
            "policy_acceptable_with_documentation_requirement",
            "policy_not_acceptable_requires_remediation_redesign",
            "policy_inconclusive_requires_expert_re_review",
        ],
        "documentation_requirement_recorded": bool(policy_decision["documentation_requirement"]),
        "other_five_obligations_carried_forward": _other_obligations_carried_forward(
            result_review
        ),
        "does_not_clear_blocker": forbidden_effect_status["blocker_fully_remediated"] is False
        and forbidden_effect_status["blocker_movement_authorized"] is False,
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
        == "review_v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_result",
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_BLOCKED",
        "consumes_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_result_review_pointer": _ptr(result_review_path),
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "execution_scope": (
            "EXECUTE_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_ONLY_NO_RELEASE_PROMOTION"
        ),
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_REMEDIATION_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "accepted_lean_dependency_evidence": {
            "command": evidence.get("command"),
            "parsed_axioms": evidence.get("parsed_axioms"),
            "project_axioms_used": evidence.get("project_axioms_used"),
            "project_axiom_count": evidence.get("project_axiom_count"),
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
        "policy_acceptance_for_standard_lean_axioms": accepted,
        "documentation_requirement_open": True,
        "expert_re_review_required": False,
        "post_adjudication_result_review_required": True,
        "tranche_001_release_blocker_status": (
            "pending_result_review_policy_acceptable_with_documentation_requirement"
        ),
        "remediation_fully_satisfied": False,
        "blocker_movement_authorized": False,
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_RELEASE_POLICY_ADJUDICATION",
        "selected_next_target_kind": "release_policy_adjudication_result_review_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_RESULT_ONLY_NO_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The policy adjudication result must be reviewed before blocker status can move.",
            },
            {
                "target": "execute_v01_alpha_dependency_remediation_tranche_002",
                "decision": "deferred",
                "reason": "The next remediation tranche remains deferred until tranche 001 policy adjudication is result-reviewed.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Release-readiness adjudication remains blocked by the pending result review and five other blockers.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 001 release-policy adjudication decides "
            "only that the standard Lean axioms [propext, Classical.choice, Quot.sound] are acceptable "
            "for the selected dependency posture with a documentation requirement and no project-local "
            "axioms. It does not clear the blocker by itself, assemble the release packet, mark "
            "v0.1-alpha readiness, discharge Lean theorem debt, reduce axiom/spec-backed proof debt, "
            "discharge retained assumptions, authorize Phase 2, close seams, validate empirically, "
            "promote the master action, promote claims, or make an external-truth claim."
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
            "Generate the v0.1-alpha dependency remediation tranche 001 release-policy adjudication."
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
        "v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_report: "
        f"accepted={payload['accepted']} classification={payload['policy_classification']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
