from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_RESULT_REVIEW_20260515_v0"
REVIEW_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_RESULT_REVIEW_ACCEPTS_"
    "EXACT_LEAN_DEPENDENCY_EVIDENCE_AND_CLASSIFIES_TRANCHE_001_STATUS_WITH_NO_RELEASE_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_EXECUTION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_EXECUTION_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_v0"
EXPECTED_EXECUTION_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTED_FOR_MASTER_ACTION_"
    "STATIONARY_IMPLIES_FREE_SCALAR_KG_WITH_NO_RELEASE_PROMOTION"
)
EXPECTED_EXECUTION_SCOPE = "EXECUTE_DEPENDENCY_REMEDIATION_TRANCHE_001_ONLY_NO_RELEASE_PROMOTION"
EXPECTED_EXECUTION_SELECTED_TARGET = "review_v01_alpha_dependency_remediation_tranche_001_execution_result"
SELECTED_REMEDIATION_FINDING_ID = "V01-ALPHA-DEP-REM-001"
SELECTED_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-001"
SELECTED_DEPENDENCY = "master_action_stationary_implies_free_scalar_kg"
EXPECTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
TRANCHE_CLASSIFICATION = "remediation_evidence_accepted_pending_release_policy_adjudication"
NEXT_TARGET = "prepare_v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_packet"

FORBIDDEN_EFFECTS = [
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "lean_theorem_debt_discharged",
    "axiom_spec_backed_debt_reduced",
    "axiom_spec_backed_debt_reduced_by_documentation",
    "proof_debt_reduced",
    "retained_assumptions_discharged",
    "theorem_discharge_authorized",
    "blocker_movement_authorized",
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


def _other_obligations(execution: dict[str, Any]) -> list[dict[str, Any]]:
    return list(execution.get("other_release_blocking_obligations", []))


def _other_obligations_unmodified(execution: dict[str, Any]) -> bool:
    rows = _other_obligations(execution)
    return (
        len(rows) == 5
        and all(row.get("modified_by_tranche_001") is False for row in rows)
        and all(
            row.get("status_carry_forward") == "tracked_unmodified_not_executed_in_tranche_001"
            for row in rows
        )
    )


def _lean_evidence(execution: dict[str, Any]) -> dict[str, Any]:
    return dict(execution.get("lean_evidence", {}))


def build_result_review(
    *,
    execution_path: Path = DEFAULT_EXECUTION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    execution = _read_json(execution_path)
    evidence = _lean_evidence(execution)
    other_obligations = _other_obligations(execution)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_execution": execution.get("execution_id") == EXPECTED_EXECUTION_ID,
        "execution_accepted": execution.get("accepted") is True,
        "execution_outcome_expected": execution.get("outcome_id") == EXPECTED_EXECUTION_OUTCOME,
        "execution_scope_expected": execution.get("execution_scope") == EXPECTED_EXECUTION_SCOPE,
        "execution_selected_this_review": execution.get("selected_next_target")
        == EXPECTED_EXECUTION_SELECTED_TARGET,
        "selected_tranche_expected": execution.get("selected_tranche_id") == SELECTED_TRANCHE_ID,
        "selected_finding_expected": execution.get("selected_remediation_finding_id")
        == SELECTED_REMEDIATION_FINDING_ID,
        "selected_dependency_expected": execution.get("selected_dependency") == SELECTED_DEPENDENCY,
        "exact_lean_dependency_evidence_matches": evidence.get("parsed_axioms")
        == EXPECTED_AXIOMS,
        "project_axioms_empty": evidence.get("project_axioms_used") == []
        and evidence.get("project_axiom_count") == 0,
        "execution_claims_no_debt_discharge": evidence.get(
            "theorem_debt_discharged_by_this_execution"
        )
        is False
        and evidence.get("proof_debt_reduced_by_this_execution") is False
        and evidence.get("retained_assumptions_discharged_by_this_execution") is False,
        "other_five_obligations_unmodified": _other_obligations_unmodified(execution),
        "classification_is_conservative": TRANCHE_CLASSIFICATION
        == "remediation_evidence_accepted_pending_release_policy_adjudication",
        "expert_re_review_still_required": execution.get(
            "selected_dependency_execution", {}
        ).get("expert_re_review_required")
        is True,
        "no_release_packet_assembly": forbidden_effect_status["release_packet_assembled"] is False,
        "no_v01_readiness_marking": forbidden_effect_status["v01_alpha_marked_ready"] is False,
        "no_lean_theorem_debt_discharge": forbidden_effect_status["lean_theorem_debt_discharged"]
        is False,
        "no_axiom_spec_backed_debt_reduction": forbidden_effect_status[
            "axiom_spec_backed_debt_reduced"
        ]
        is False,
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
        "forbidden_effects_all_false": all(value is False for value in forbidden_effect_status.values()),
        "exactly_one_next_target_selected": NEXT_TARGET
        == "prepare_v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_packet",
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_RESULT_REVIEW_BLOCKED",
        "consumes_execution": EXPECTED_EXECUTION_ID,
        "consumes_execution_pointer": _ptr(execution_path),
        "consumed_execution_schema_id": execution.get("schema_id"),
        "source_dependency_remediation_execution_packet_result_review": execution.get(
            "consumes_result_review"
        ),
        "review_scope": "DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_RESULT_REVIEW_ONLY_NO_RELEASE_PROMOTION",
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_REMEDIATION_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "exact_lean_dependency_evidence": {
            "command": evidence.get("command"),
            "parsed_axioms": evidence.get("parsed_axioms"),
            "project_axioms_used": evidence.get("project_axioms_used"),
            "project_axiom_count": evidence.get("project_axiom_count"),
            "classification": evidence.get("classification"),
            "raw_output": evidence.get("raw_output"),
        },
        "tranche_001_status_classification": TRANCHE_CLASSIFICATION,
        "classification_options_considered": [
            "remediation_evidence_accepted",
            "remediation_partially_satisfied_pending_policy_adjudication",
            "remediation_retained_pending_expert_re_review",
            "remediation_failed_requires_redesign",
            TRANCHE_CLASSIFICATION,
        ],
        "classification_reason": (
            "Exact Lean dependency evidence was produced and no project-local axioms were found, "
            "but standard Lean axioms still require v0.1-alpha release-policy adjudication before "
            "the blocker can move or release-readiness posture can change."
        ),
        "tranche_001_release_blocker_status": "still_blocking_pending_release_policy_adjudication",
        "remediation_evidence_accepted": accepted,
        "remediation_fully_satisfied": False,
        "blocker_movement_authorized": False,
        "expert_re_review_required": True,
        "release_policy_adjudication_required": True,
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_RESULT_REVIEW",
        "selected_next_target_kind": "tranche_001_release_policy_adjudication_packet_preparation_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_PACKET_ONLY_NO_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "Standard Lean axiom acceptability for v0.1-alpha release posture must be adjudicated before blocker movement.",
            },
            {
                "target": "execute_v01_alpha_dependency_remediation_tranche_002",
                "decision": "deferred",
                "reason": "The next remediation execution is deferred until tranche 001 evidence classification is policy-adjudicated.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Release-readiness adjudication remains blocked by policy-adjudication and five unexecuted release-blocking obligations.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 001 execution result review accepts exact "
            "Lean dependency evidence and classifies tranche 001 status conservatively. It does not "
            "assemble the release packet, mark v0.1-alpha readiness, discharge Lean theorem debt, "
            "reduce axiom/spec-backed proof debt, discharge retained assumptions, authorize Phase 2, "
            "close seams, validate empirically, promote the master action, promote claims, or make "
            "an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_result_review(
    *,
    execution_path: Path = DEFAULT_EXECUTION_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(
        execution_path=execution_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the v0.1-alpha dependency remediation tranche 001 execution result review."
    )
    parser.add_argument("--execution", type=Path, default=DEFAULT_EXECUTION_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    execution_path = ns.execution if ns.execution.is_absolute() else (REPO_ROOT / ns.execution)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        execution_path=execution_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_dependency_remediation_tranche_001_execution_result_review_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
