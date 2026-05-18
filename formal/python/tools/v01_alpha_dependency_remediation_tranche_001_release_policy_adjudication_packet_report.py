from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_PACKET_20260515_v0"
)
PACKET_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_PACKET_v0"
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_PACKET_"
    "PREPARED_WITH_NO_POLICY_DECISION_OR_RELEASE_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_PACKET_20260515_v0.json"
)

EXPECTED_RESULT_REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_RESULT_REVIEW_v0"
)
EXPECTED_RESULT_REVIEW_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_RESULT_REVIEW_ACCEPTS_"
    "EXACT_LEAN_DEPENDENCY_EVIDENCE_AND_CLASSIFIES_TRANCHE_001_STATUS_WITH_NO_RELEASE_PROMOTION"
)
EXPECTED_RESULT_REVIEW_SELECTED_TARGET = (
    "prepare_v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_packet"
)
EXPECTED_TRANCHE_CLASSIFICATION = (
    "remediation_evidence_accepted_pending_release_policy_adjudication"
)
SELECTED_REMEDIATION_FINDING_ID = "V01-ALPHA-DEP-REM-001"
SELECTED_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-001"
SELECTED_DEPENDENCY = "master_action_stationary_implies_free_scalar_kg"
EXPECTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
NEXT_TARGET = (
    "review_v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_packet_result"
)

FORBIDDEN_EFFECTS = [
    "policy_adjudication_executed",
    "release_policy_decision_made",
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


def _exact_evidence(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("exact_lean_dependency_evidence", {}))


def _other_obligations(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("other_release_blocking_obligations", []))


def _other_obligations_tracked(result_review: dict[str, Any]) -> bool:
    rows = _other_obligations(result_review)
    return (
        len(rows) == 5
        and all(row.get("modified_by_tranche_001") is False for row in rows)
        and all(
            row.get("status_carry_forward") == "tracked_unmodified_not_executed_in_tranche_001"
            for row in rows
        )
    )


def _release_policy_acceptance_criteria() -> list[str]:
    return [
        "The later adjudication cites the exact accepted Lean dependency evidence for the selected dependency.",
        "The later adjudication explicitly evaluates propext, Classical.choice, and Quot.sound under the v0.1-alpha release policy.",
        "The later adjudication preserves project_axioms_used as an empty list unless new formal evidence is produced.",
        "The later adjudication records whether expert re-review accepts the standard Lean axiom posture for this dependency.",
        "Any blocker downgrade is limited to tranche 001 and does not affect the other five release-blocking obligations.",
        "No theorem debt, proof debt, retained assumption, release-readiness, or promotion claim is inferred from policy acceptance alone.",
    ]


def _release_policy_failure_criteria() -> list[str]:
    return [
        "The later adjudication omits one or more of propext, Classical.choice, or Quot.sound.",
        "The later adjudication treats an empty project_axioms_used list as a theorem/proof-debt discharge.",
        "The later adjudication downgrades the selected blocker without a recorded v0.1-alpha policy decision.",
        "The later adjudication modifies or clears any of the other five release-blocking obligations.",
        "The later adjudication assembles the release packet, marks readiness, authorizes Phase 2, closes seams, validates empirically, or promotes the master action.",
        "The later adjudication skips the required expert re-review disposition for this dependency posture.",
    ]


def build_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    evidence = _exact_evidence(result_review)
    other_obligations = _other_obligations(result_review)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    policy_question = (
        "Are [propext, Classical.choice, Quot.sound] acceptable under the v0.1-alpha "
        "release policy for master_action_stationary_implies_free_scalar_kg, given that "
        "project_axioms_used is empty?"
    )

    acceptance_criteria = {
        "consumes_expected_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_accepted": result_review.get("accepted") is True,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_selected_this_packet": result_review.get("selected_next_target")
        == EXPECTED_RESULT_REVIEW_SELECTED_TARGET,
        "selected_tranche_expected": result_review.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID,
        "selected_finding_expected": result_review.get("selected_remediation_finding_id")
        == SELECTED_REMEDIATION_FINDING_ID,
        "selected_dependency_expected": result_review.get("selected_dependency")
        == SELECTED_DEPENDENCY,
        "accepted_lean_dependency_evidence_preserved_exactly": evidence.get("parsed_axioms")
        == EXPECTED_AXIOMS,
        "project_axioms_used_empty_preserved": evidence.get("project_axioms_used") == []
        and evidence.get("project_axiom_count") == 0,
        "prior_classification_requires_policy_adjudication": result_review.get(
            "tranche_001_status_classification"
        )
        == EXPECTED_TRANCHE_CLASSIFICATION
        and result_review.get("release_policy_adjudication_required") is True,
        "policy_question_defined": policy_question
        == (
            "Are [propext, Classical.choice, Quot.sound] acceptable under the v0.1-alpha "
            "release policy for master_action_stationary_implies_free_scalar_kg, given that "
            "project_axioms_used is empty?"
        ),
        "release_policy_acceptance_criteria_defined": len(
            _release_policy_acceptance_criteria()
        )
        >= 6,
        "release_policy_failure_criteria_defined": len(_release_policy_failure_criteria()) >= 6,
        "expert_re_review_requirement_preserved": result_review.get("expert_re_review_required")
        is True,
        "other_five_obligations_tracked": _other_obligations_tracked(result_review),
        "prepares_policy_adjudication_only": forbidden_effect_status[
            "policy_adjudication_executed"
        ]
        is False,
        "no_policy_decision_made": forbidden_effect_status["release_policy_decision_made"]
        is False,
        "blocker_not_fully_remediated": forbidden_effect_status["blocker_fully_remediated"]
        is False,
        "no_theorem_or_proof_debt_discharge": forbidden_effect_status[
            "lean_theorem_debt_discharged"
        ]
        is False
        and forbidden_effect_status["proof_debt_reduced"] is False
        and forbidden_effect_status["axiom_spec_backed_debt_reduced"] is False,
        "no_release_packet_assembly_or_readiness_marking": forbidden_effect_status[
            "release_packet_assembled"
        ]
        is False
        and forbidden_effect_status["v01_alpha_marked_ready"] is False,
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
        == "review_v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_packet_result",
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_PACKET_BLOCKED",
        "consumes_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_result_review_pointer": _ptr(result_review_path),
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "source_execution": result_review.get("consumes_execution"),
        "packet_scope": (
            "PREPARE_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_PACKET_ONLY_"
            "NO_POLICY_DECISION_OR_RELEASE_PROMOTION"
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
        "policy_question": policy_question,
        "release_policy_acceptance_criteria": _release_policy_acceptance_criteria(),
        "release_policy_failure_criteria": _release_policy_failure_criteria(),
        "expert_re_review_required": True,
        "expert_re_review_requirement": (
            "A later adjudication must record expert re-review disposition for whether the "
            "standard Lean axiom posture is acceptable for tranche 001 under v0.1-alpha policy."
        ),
        "blocker_may_be_downgraded_after_adjudication": (
            "only_if_later_policy_adjudication_accepts_standard_lean_axiom_posture"
        ),
        "blocker_downgrade_allowed_by_this_packet": False,
        "tranche_001_release_blocker_status": (
            "still_blocking_pending_release_policy_adjudication_execution"
        ),
        "policy_decision_made": False,
        "policy_adjudication_executed": False,
        "remediation_fully_satisfied": False,
        "blocker_movement_authorized": False,
        "other_release_blocking_obligations": other_obligations,
        "other_release_blocking_obligation_count": len(other_obligations),
        "post_adjudication_review_target": (
            "review_v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_result"
        ),
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_POLICY_PACKET",
        "selected_next_target_kind": "release_policy_adjudication_packet_result_review_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_PACKET_ONLY_NO_POLICY_DECISION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The policy-adjudication packet must be reviewed before any policy decision can execute.",
            },
            {
                "target": "execute_v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication",
                "decision": "deferred",
                "reason": "The policy decision remains blocked until the packet result review authorizes execution.",
            },
            {
                "target": "execute_v01_alpha_dependency_remediation_tranche_002",
                "decision": "deferred",
                "reason": "The next remediation tranche remains deferred while tranche 001 policy meaning is adjudicated.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Release-readiness adjudication remains blocked by tranche 001 policy adjudication and five other blockers.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 001 release-policy adjudication packet "
            "prepares a policy-decision wrapper only. It preserves exact Lean dependency evidence "
            "and empty project-local axiom evidence, but does not make the policy decision, clear "
            "the blocker, assemble the release packet, mark v0.1-alpha readiness, discharge Lean "
            "theorem debt, reduce axiom/spec-backed proof debt, discharge retained assumptions, "
            "authorize Phase 2, close seams, validate empirically, promote the master action, "
            "promote claims, or make an external-truth claim."
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
            "Generate the v0.1-alpha dependency remediation tranche 001 release-policy "
            "adjudication packet."
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
        "v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_packet_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
