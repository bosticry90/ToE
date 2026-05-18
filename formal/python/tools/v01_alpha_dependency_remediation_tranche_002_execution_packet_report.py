from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_20260515_v0"
PACKET_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_v0"
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_PREPARED_FOR_"
    "STATIONARY_IMPLIES_OPERATOR_ZERO_WITH_NO_REMEDIATION_EXECUTION_OR_RELEASE_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_SELECTION_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_20260515_v0.json"
)

EXPECTED_SELECTION_RESULT_REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_RESULT_REVIEW_v0"
)
EXPECTED_SELECTION_RESULT_REVIEW_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_RESULT_REVIEW_ACCEPTS_"
    "TRANCHE_002_SELECTION_AND_AUTHORIZES_TRANCHE_002_EXECUTION_PACKET_PREPARATION_ONLY"
)
EXPECTED_SELECTION_RESULT_REVIEW_SELECTED_TARGET = (
    "prepare_v01_alpha_dependency_remediation_tranche_002_execution_packet"
)
TRANCHE_001_STATUS = "documented_dependency_nonblocking"
SELECTED_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-002"
SELECTED_FINDING_ID = "V01-ALPHA-DEP-REM-002"
SELECTED_DEPENDENCY = "stationary_implies_operator_zero"
SELECTED_DEPENDENCY_CLASS = "lean_theorem_dependency"
LEAN_TARGET = "ToeFormal.QFT.FreeScalarDerivation.stationary_implies_operator_zero"
LEAN_SOURCE = "formal/toe_formal/ToeFormal/QFT/FreeScalarDerivation.lean"
LEAN_AUDIT_COMMAND = (
    "#print axioms ToeFormal.QFT.FreeScalarDerivation.stationary_implies_operator_zero"
)
NEXT_TARGET = "review_v01_alpha_dependency_remediation_tranche_002_execution_packet_result"

FORBIDDEN_EFFECTS = [
    "remediation_execution_authorized",
    "remediation_executed",
    "lean_dependency_audit_executed",
    "lean_dependency_evidence_captured",
    "documentation_prepared",
    "expert_re_review_executed",
    "blocker_movement_registered",
    "blocker_fully_remediated",
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


def _release_blocking_obligations(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("remaining_release_blocking_obligations", []))


def _selected_row(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("selected_next_remediation_tranche", {}))


def _selected_obligation(rows: list[dict[str, Any]]) -> dict[str, Any]:
    for row in rows:
        if row.get("dependency_finding_id") == SELECTED_FINDING_ID:
            return dict(row)
    return {}


def _obligations_are_unmodified(rows: list[dict[str, Any]]) -> bool:
    return (
        len(rows) == 5
        and all(row.get("modified_by_tranche_001") is False for row in rows)
        and all(
            row.get("status_carry_forward") == "tracked_unmodified_not_executed_in_tranche_001"
            for row in rows
        )
    )


def build_packet(
    *,
    selection_result_review_path: Path = DEFAULT_SELECTION_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(selection_result_review_path)
    release_blocking_obligations = _release_blocking_obligations(result_review)
    selected_row = _selected_row(result_review)
    selected_obligation = _selected_obligation(release_blocking_obligations)
    nonselected_obligations = [
        row
        for row in release_blocking_obligations
        if row.get("dependency_finding_id") != SELECTED_FINDING_ID
    ]
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    execution_scope = {
        "scope_kind": "LEAN_DEPENDENCY_AUDIT_CAPTURE_FOR_SELECTED_TRANCHE_ONLY",
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_dependency_finding_id": SELECTED_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "allowed_execution_actions": [
            "run_the_pinned_lean_axiom_audit_command_for_the_selected_target",
            "record_raw_lean_axiom_output_for_the_selected_target",
            "parse_standard_lean_axioms_and_project_local_axioms_for_the_selected_target",
            "carry_forward_all_nonselected_release_blockers_without_modification",
        ],
        "forbidden_execution_actions": [
            "execute_any_nonselected_remediation_tranche",
            "claim_theorem_or_proof_debt_discharge_from_audit_text",
            "register_blocker_movement",
            "assemble_release_packet",
            "mark_v01_alpha_ready",
            "authorize_phase2_or_seam_or_empirical_or_master_action_movement",
        ],
    }
    required_evidence_surface = {
        "surface_kind": "lean_axiom_audit_readout",
        "lean_target": LEAN_TARGET,
        "lean_source": LEAN_SOURCE,
        "audit_command": LEAN_AUDIT_COMMAND,
        "raw_output_required": True,
        "parsed_axioms_required": True,
        "project_axioms_used_required": True,
        "execution_status": "prepared_not_executed_v0",
    }
    documentation_requirement = {
        "required": "conditional_after_execution_result_review",
        "condition": (
            "Required if the captured dependency posture is policy-acceptable but needs "
            "release-facing documentation, or if any project-local axiom posture needs explanation."
        ),
        "prepared_by_this_packet": False,
    }
    expert_re_review_requirement = {
        "required": "conditional_after_execution_result_review",
        "trigger": (
            "Triggered by project-local axioms, unexpected nonstandard axioms, target mismatch, "
            "or evidence ambiguity in the execution result."
        ),
        "executed_by_this_packet": False,
    }
    success_criteria = [
        "execution_consumes_this_packet_and_targets_only_stationary_implies_operator_zero",
        "raw_lean_axiom_output_is_recorded_for_the_pinned_audit_command",
        "parsed_axioms_and_project_axioms_used_are_recorded",
        "nonselected_release_blockers_are_carried_forward_unmodified",
        "no_release_readiness_or_debt_discharge_is_claimed_by_execution_text",
    ]
    failure_criteria = [
        "execution_targets_a_dependency_other_than_stationary_implies_operator_zero",
        "lean_audit_output_is_missing_or_not_parseable",
        "project_local_axioms_are_detected_without_escalation",
        "execution_claims_release_readiness_or_theorem_debt_discharge",
        "nonselected_release_blockers_are_modified",
    ]

    acceptance_criteria = {
        "consumes_expected_selection_result_review": result_review.get("review_id")
        == EXPECTED_SELECTION_RESULT_REVIEW_ID,
        "selection_result_review_accepted": result_review.get("accepted") is True,
        "selection_result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_SELECTION_RESULT_REVIEW_OUTCOME,
        "selection_result_review_selected_this_packet": result_review.get("selected_next_target")
        == EXPECTED_SELECTION_RESULT_REVIEW_SELECTED_TARGET,
        "tranche_001_documented_nonblocking_preserved": result_review.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS,
        "tranche_002_selected_only": result_review.get("selection_count") == 1
        and result_review.get("selected_next_tranche_id") == SELECTED_TRANCHE_ID
        and selected_row.get("selected_tranche_id") == SELECTED_TRANCHE_ID,
        "selected_dependency_expected": result_review.get("selected_next_dependency")
        == SELECTED_DEPENDENCY
        and selected_row.get("selected_dependency") == SELECTED_DEPENDENCY,
        "selected_finding_expected": result_review.get("selected_next_dependency_finding_id")
        == SELECTED_FINDING_ID
        and selected_obligation.get("dependency_finding_id") == SELECTED_FINDING_ID,
        "selected_dependency_class_expected": result_review.get("selected_next_dependency_class")
        == SELECTED_DEPENDENCY_CLASS
        and selected_obligation.get("dependency_class") == SELECTED_DEPENDENCY_CLASS,
        "all_five_release_blockers_carried_forward": _obligations_are_unmodified(
            release_blocking_obligations
        ),
        "execution_scope_defined": execution_scope["selected_dependency"] == SELECTED_DEPENDENCY
        and execution_scope["scope_kind"]
        == "LEAN_DEPENDENCY_AUDIT_CAPTURE_FOR_SELECTED_TRANCHE_ONLY",
        "lean_audit_target_defined": required_evidence_surface["lean_target"] == LEAN_TARGET
        and required_evidence_surface["audit_command"] == LEAN_AUDIT_COMMAND,
        "documentation_requirement_defined": documentation_requirement["required"]
        == "conditional_after_execution_result_review",
        "expert_re_review_requirement_defined": expert_re_review_requirement["required"]
        == "conditional_after_execution_result_review",
        "success_and_failure_criteria_defined": len(success_criteria) >= 5
        and len(failure_criteria) >= 5,
        "packet_prepares_without_execution": forbidden_effect_status[
            "remediation_executed"
        ]
        is False
        and forbidden_effect_status["lean_dependency_audit_executed"] is False
        and forbidden_effect_status["lean_dependency_evidence_captured"] is False,
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
        == "review_v01_alpha_dependency_remediation_tranche_002_execution_packet_result",
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_BLOCKED",
        "consumes_selection_result_review": EXPECTED_SELECTION_RESULT_REVIEW_ID,
        "consumes_selection_result_review_pointer": _ptr(selection_result_review_path),
        "consumed_selection_result_review_schema_id": result_review.get("schema_id"),
        "packet_scope": (
            "PREPARE_TRANCHE_002_EXECUTION_PACKET_ONLY_NO_REMEDIATION_EXECUTION_OR_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_001_formal_movement_accepted": True,
        "tranche_001_cleared_for_global_release_readiness": False,
        "global_release_readiness_still_blocked": True,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "selected_release_blocking_obligation": selected_obligation,
        "release_blocking_obligations_carry_forward": release_blocking_obligations,
        "release_blocking_obligation_count": len(release_blocking_obligations),
        "nonselected_release_blocking_obligations": nonselected_obligations,
        "nonselected_release_blocking_obligation_count": len(nonselected_obligations),
        "tranche_002_execution_packet_prepared": accepted,
        "execution_packet_prepared": accepted,
        "execution_scope": execution_scope,
        "required_evidence_surface": required_evidence_surface,
        "lean_dependency_audit_target": {
            "lean_target": LEAN_TARGET,
            "lean_source": LEAN_SOURCE,
            "audit_command": LEAN_AUDIT_COMMAND,
            "executed_by_this_packet": False,
        },
        "documentation_requirement": documentation_requirement,
        "expert_re_review_requirement": expert_re_review_requirement,
        "success_criteria": success_criteria,
        "failure_criteria": failure_criteria,
        "post_packet_review_target": NEXT_TARGET,
        "post_execution_adjudication_target": (
            "review_v01_alpha_dependency_remediation_tranche_002_execution_result"
        ),
        "remediation_execution_authorized": False,
        "remediation_executed": False,
        "lean_dependency_audit_executed": False,
        "lean_dependency_evidence_captured": False,
        "documentation_prepared": False,
        "expert_re_review_executed": False,
        "blocker_movement_registered": False,
        "blocker_fully_remediated": False,
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET",
        "selected_next_target_kind": "tranche_002_execution_packet_result_review_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_TRANCHE_002_EXECUTION_PACKET_RESULT_ONLY_NO_REMEDIATION_EXECUTION_OR_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The tranche 002 execution packet must be reviewed before remediation execution can be authorized.",
            },
            {
                "target": "execute_v01_alpha_dependency_remediation_tranche_002",
                "decision": "deferred",
                "reason": "Actual tranche 002 execution is deferred until this packet is reviewed and accepted.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Release-readiness adjudication remains blocked by the five tracked release-blocking obligations.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 002 execution packet prepares only "
            "a bounded Lean dependency-audit execution scope for V01-ALPHA-DEP-REM-002 / "
            "stationary_implies_operator_zero. It does not execute remediation, run the Lean "
            "audit, capture dependency evidence, prepare documentation, execute expert re-review, "
            "register blocker movement, assemble the release packet, mark v0.1-alpha readiness, "
            "discharge Lean theorem debt, reduce axiom/spec-backed proof debt, discharge retained "
            "assumptions, authorize Phase 2, close seams, validate empirically, promote the master "
            "action, promote claims, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_packet(
    *,
    selection_result_review_path: Path = DEFAULT_SELECTION_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_packet(
        selection_result_review_path=selection_result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the v0.1-alpha dependency remediation tranche 002 execution packet."
    )
    parser.add_argument(
        "--selection-result-review",
        type=Path,
        default=DEFAULT_SELECTION_RESULT_REVIEW_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    selection_result_review_path = (
        ns.selection_result_review
        if ns.selection_result_review.is_absolute()
        else (REPO_ROOT / ns.selection_result_review)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_packet(
        selection_result_review_path=selection_result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_dependency_remediation_tranche_002_execution_packet_report: "
        f"accepted={payload['accepted']} selected_dependency={payload['selected_dependency']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
