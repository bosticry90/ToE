from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_RELEASE_POLICY_ADJUDICATION_RESULT_REVIEW_20260515_v0"
)
REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_RELEASE_POLICY_ADJUDICATION_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_RELEASE_POLICY_ADJUDICATION_RESULT_REVIEW_"
    "ACCEPTS_POLICY_ACCEPTABLE_WITH_DOCUMENTATION_REQUIREMENT_AND_AUTHORIZES_DOCUMENTATION_PACKET_PREPARATION_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_ADJUDICATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_RELEASE_POLICY_ADJUDICATION_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_RELEASE_POLICY_ADJUDICATION_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_ADJUDICATION_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_RELEASE_POLICY_ADJUDICATION_v0"
EXPECTED_ADJUDICATION_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_RELEASE_POLICY_ADJUDICATED_"
    "WITH_NO_RELEASE_PROMOTION"
)
EXPECTED_ADJUDICATION_SELECTED_TARGET = (
    "review_v01_alpha_dependency_remediation_tranche_002_release_policy_adjudication_result"
)
TRANCHE_001_STATUS = "documented_dependency_nonblocking"
SELECTED_REMEDIATION_FINDING_ID = "V01-ALPHA-DEP-REM-002"
SELECTED_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-002"
SELECTED_DEPENDENCY = "stationary_implies_operator_zero"
SELECTED_DEPENDENCY_CLASS = "lean_theorem_dependency"
LEAN_TARGET = "ToeFormal.QFT.FreeScalarDerivation.stationary_implies_operator_zero"
EXPECTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
POLICY_CLASSIFICATION = "policy_acceptable_with_documentation_requirement"
RESULT_REVIEW_CLASSIFICATION = "policy_adjudicated_nonblocking_pending_documentation"
NEXT_TARGET = "prepare_v01_alpha_dependency_remediation_tranche_002_documentation_packet"

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
    "documentation_packet_prepared",
    "documentation_execution_performed",
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


def _accepted_evidence(adjudication: dict[str, Any]) -> dict[str, Any]:
    return dict(adjudication.get("accepted_lean_dependency_evidence", {}))


def _policy_decision(adjudication: dict[str, Any]) -> dict[str, Any]:
    return dict(adjudication.get("policy_decision", {}))


def _release_blockers(adjudication: dict[str, Any]) -> list[dict[str, Any]]:
    return list(adjudication.get("release_blocking_obligations_carry_forward", []))


def _other_obligations(adjudication: dict[str, Any]) -> list[dict[str, Any]]:
    return list(adjudication.get("other_release_blocking_obligations", []))


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


def build_result_review(
    *,
    adjudication_path: Path = DEFAULT_ADJUDICATION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    adjudication = _read_json(adjudication_path)
    evidence = _accepted_evidence(adjudication)
    decision = _policy_decision(adjudication)
    release_blockers = _release_blockers(adjudication)
    other_obligations = _other_obligations(adjudication)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_adjudication": adjudication.get("execution_id")
        == EXPECTED_ADJUDICATION_ID,
        "adjudication_accepted": adjudication.get("accepted") is True
        and adjudication.get("executed") is True,
        "adjudication_outcome_expected": adjudication.get("outcome_id")
        == EXPECTED_ADJUDICATION_OUTCOME,
        "adjudication_selected_this_review": adjudication.get("selected_next_target")
        == EXPECTED_ADJUDICATION_SELECTED_TARGET,
        "selected_tranche_expected": adjudication.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID,
        "selected_finding_expected": adjudication.get("selected_remediation_finding_id")
        == SELECTED_REMEDIATION_FINDING_ID,
        "selected_dependency_expected": adjudication.get("selected_dependency")
        == SELECTED_DEPENDENCY,
        "selected_dependency_class_expected": adjudication.get("selected_dependency_class")
        == SELECTED_DEPENDENCY_CLASS,
        "tranche_001_documented_nonblocking_preserved": adjudication.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS,
        "lean_audit_target_preserved": adjudication.get("lean_audit_target", {}).get(
            "lean_target"
        )
        == LEAN_TARGET,
        "policy_classification_exact": adjudication.get("policy_classification")
        == POLICY_CLASSIFICATION
        and decision.get("classification") == POLICY_CLASSIFICATION,
        "exact_lean_dependency_evidence_preserved": evidence.get("parsed_axioms")
        == EXPECTED_AXIOMS
        and evidence.get("exact_axioms_or_dependencies_used") == EXPECTED_AXIOMS
        and evidence.get("standard_lean_axioms_used") == EXPECTED_AXIOMS
        and decision.get("standard_lean_axioms_reviewed") == EXPECTED_AXIOMS,
        "project_axioms_used_empty": evidence.get("project_axioms_used") == []
        and evidence.get("project_axiom_count") == 0
        and decision.get("project_axioms_used") == []
        and decision.get("project_axiom_count") == 0,
        "documentation_requirement_remains_open": adjudication.get(
            "documentation_requirement_open"
        )
        is True
        and bool(decision.get("documentation_requirement")),
        "blocker_not_cleared": adjudication.get("remediation_fully_satisfied") is False
        and adjudication.get("blocker_movement_authorized") is False
        and adjudication.get("blocker_movement_registered") is False
        and decision.get("does_not_clear_blocker_by_itself") is True,
        "release_blockers_remain_tracked": _release_blockers_tracked(release_blockers),
        "other_four_obligations_carried_forward": _other_obligations_carried_forward(
            other_obligations
        ),
        "no_documentation_packet_prepared": forbidden_effect_status[
            "documentation_packet_prepared"
        ]
        is False,
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
        == "prepare_v01_alpha_dependency_remediation_tranche_002_documentation_packet",
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_RELEASE_POLICY_ADJUDICATION_RESULT_REVIEW_BLOCKED",
        "consumes_adjudication": EXPECTED_ADJUDICATION_ID,
        "consumes_adjudication_pointer": _ptr(adjudication_path),
        "consumed_adjudication_schema_id": adjudication.get("schema_id"),
        "source_policy_packet_result_review": adjudication.get("consumes_result_review"),
        "review_scope": (
            "REVIEW_TRANCHE_002_RELEASE_POLICY_ADJUDICATION_RESULT_ONLY_"
            "AUTHORIZE_DOCUMENTATION_PACKET_PREPARATION_NO_BLOCKER_MOVEMENT"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_REMEDIATION_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "lean_audit_target": adjudication.get("lean_audit_target"),
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
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "policy_decision_reviewed": decision,
        "documentation_requirement_open": True,
        "documentation_packet_preparation_authorized": accepted,
        "documentation_packet_prepared": False,
        "documentation_execution_performed": False,
        "tranche_002_policy_status": "policy_acceptable_documentation_required",
        "tranche_002_release_blocker_status": "still_blocking_pending_documentation_packet",
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_RELEASE_POLICY_ADJUDICATION_RESULT_REVIEW",
        "selected_next_target_kind": "documentation_packet_preparation_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_TRANCHE_002_DOCUMENTATION_PACKET_ONLY_NO_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The policy adjudication is acceptable with documentation required, so prepare the tranche 002 documentation packet next.",
            },
            {
                "target": "prepare_v01_alpha_dependency_remediation_tranche_002_status_adjudication_packet",
                "decision": "deferred",
                "reason": "Status adjudication remains deferred until tranche 002 documentation is prepared and reviewed.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Release-readiness adjudication remains blocked by tranche 002 documentation and the remaining tracked blockers.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 002 release-policy adjudication result "
            "review accepts policy_acceptable_with_documentation_requirement and authorizes only "
            "documentation packet preparation. It does not prepare documentation itself, clear or "
            "move the blocker, assemble the release packet, mark v0.1-alpha readiness, discharge "
            "Lean theorem debt, reduce axiom/spec-backed proof debt, discharge retained assumptions, "
            "authorize Phase 2, close seams, validate empirically, promote the master action, promote "
            "claims, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_result_review(
    *,
    adjudication_path: Path = DEFAULT_ADJUDICATION_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(
        adjudication_path=adjudication_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha dependency remediation tranche 002 release-policy "
            "adjudication result review."
        )
    )
    parser.add_argument("--adjudication", type=Path, default=DEFAULT_ADJUDICATION_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    adjudication_path = (
        ns.adjudication if ns.adjudication.is_absolute() else (REPO_ROOT / ns.adjudication)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        adjudication_path=adjudication_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_dependency_remediation_tranche_002_release_policy_adjudication_result_review_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
