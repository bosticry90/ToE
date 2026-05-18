from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_DOCUMENTATION_PACKET_20260515_v0"
PACKET_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_DOCUMENTATION_PACKET_v0"
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_DOCUMENTATION_PACKET_PREPARED_"
    "WITH_NO_BLOCKER_CLEARANCE_OR_RELEASE_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_RELEASE_POLICY_ADJUDICATION_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_DOCUMENTATION_PACKET_20260515_v0.json"
)
DEFAULT_DOCUMENTATION_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_DOCUMENTATION_v0.md"
)

EXPECTED_RESULT_REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_RELEASE_POLICY_ADJUDICATION_RESULT_REVIEW_v0"
)
EXPECTED_RESULT_REVIEW_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_RELEASE_POLICY_ADJUDICATION_RESULT_REVIEW_"
    "ACCEPTS_POLICY_ACCEPTABLE_WITH_DOCUMENTATION_REQUIREMENT_AND_AUTHORIZES_DOCUMENTATION_PACKET_PREPARATION_ONLY"
)
EXPECTED_RESULT_REVIEW_SELECTED_TARGET = (
    "prepare_v01_alpha_dependency_remediation_tranche_003_documentation_packet"
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
RESULT_REVIEW_CLASSIFICATION = "policy_adjudicated_nonblocking_pending_documentation"
NEXT_TARGET = "review_v01_alpha_dependency_remediation_tranche_003_documentation_packet_result"

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


def _accepted_evidence(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("accepted_lean_dependency_evidence", {}))


def _policy_decision(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("policy_decision_reviewed", {}))


def _release_blockers(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("release_blocking_obligations_carry_forward", []))


def _other_obligations(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("other_release_blocking_obligations", []))


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


def build_documentation_markdown(result_review: dict[str, Any]) -> str:
    evidence = _accepted_evidence(result_review)
    decision = _policy_decision(result_review)
    lean_target = result_review.get("lean_audit_target", {})
    other_obligations = _other_obligations(result_review)
    axiom_readout = "[" + ", ".join(evidence.get("parsed_axioms", [])) + "]"
    other_lines = "\n".join(
        f"- `{row.get('dependency_finding_id')}` / `{row.get('dependency')}`: "
        f"{row.get('status_carry_forward')}"
        for row in other_obligations
    )

    return (
        "# v0.1-alpha dependency remediation tranche 003 documentation\n\n"
        "## Scope\n\n"
        f"- Selected finding: `{SELECTED_REMEDIATION_FINDING_ID}`\n"
        f"- Selected tranche: `{SELECTED_TRANCHE_ID}`\n"
        f"- Selected dependency: `{SELECTED_DEPENDENCY}`\n"
        f"- Lean audit target: `{lean_target.get('lean_target')}`\n"
        f"- Policy classification: `{POLICY_CLASSIFICATION}`\n"
        "- Documentation purpose: record the standard Lean axiom posture required by the "
        "v0.1-alpha release-policy adjudication result review.\n\n"
        "## Accepted Lean Dependency Posture\n\n"
        f"- Accepted Lean dependencies: `{axiom_readout}`\n"
        f"- Project-local axioms used: `project_axioms_used = {evidence.get('project_axioms_used')}`\n"
        f"- Project-local axiom count: `{evidence.get('project_axiom_count')}`\n"
        f"- Lean evidence command: `{lean_target.get('command')}`\n\n"
        "The dependency posture is acceptable for v0.1-alpha because the only recorded "
        "axioms are standard Lean/mathlib axiomatic dependencies and no project-local "
        "axioms are present. This documentation records that posture for the selected "
        "dependency only.\n\n"
        "## What This Documentation Does Not Prove\n\n"
        "- It does not prove `finite_transport_theorems_construct_residual_package_v0`.\n"
        "- It does not discharge Lean theorem debt or proof debt.\n"
        "- It does not discharge retained assumptions.\n"
        "- It does not clear `V01-ALPHA-DEP-REM-003` by itself.\n"
        "- It does not register blocker movement for tranche 003.\n"
        "- It does not assemble the v0.1-alpha release packet or mark release readiness.\n"
        "- It does not authorize Phase 2, seam closure, empirical validation, or master-action promotion.\n\n"
        "## Policy Rationale\n\n"
        f"{decision.get('decision')}\n\n"
        f"{decision.get('documentation_requirement')}\n\n"
        "Project-local axioms remain absent because the accepted evidence records "
        "`project_axioms_used = []` and `project_axiom_count = 0`. Any later change to "
        "that evidence requires a separate review surface.\n\n"
        "## Blocker Movement Boundary\n\n"
        "Blocker movement still requires result review of this documentation packet, "
        "later status adjudication, and a separate movement-registration path. This "
        "documentation packet prepares the evidence surface only; it does not downgrade, "
        "clear, or otherwise move the blocker.\n\n"
        "## Prior Tranche Carry-Forward\n\n"
        f"- Tranche 001 status: `{result_review.get('tranche_001_status')}`\n"
        f"- Tranche 002 status: `{result_review.get('tranche_002_status')}`\n\n"
        "## Other Release-Blocking Obligations\n\n"
        f"{other_lines}\n"
    )


def build_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    documentation_path: Path = DEFAULT_DOCUMENTATION_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    evidence = _accepted_evidence(result_review)
    decision = _policy_decision(result_review)
    release_blockers = _release_blockers(result_review)
    other_obligations = _other_obligations(result_review)
    lean_target = result_review.get("lean_audit_target", {})
    documentation_markdown = build_documentation_markdown(result_review)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_accepted": result_review.get("accepted") is True,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_selected_this_packet": result_review.get("selected_next_target")
        == EXPECTED_RESULT_REVIEW_SELECTED_TARGET,
        "documentation_packet_preparation_authorized": result_review.get(
            "documentation_packet_preparation_authorized"
        )
        is True,
        "selected_tranche_expected": result_review.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID,
        "selected_finding_expected": result_review.get("selected_remediation_finding_id")
        == SELECTED_REMEDIATION_FINDING_ID,
        "selected_dependency_expected": result_review.get("selected_dependency")
        == SELECTED_DEPENDENCY,
        "selected_dependency_class_expected": result_review.get("selected_dependency_class")
        == SELECTED_DEPENDENCY_CLASS,
        "tranche_001_documented_nonblocking_preserved": result_review.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": result_review.get(
            "tranche_002_status"
        )
        == TRANCHE_002_STATUS,
        "lean_audit_target_preserved": lean_target.get("lean_target") == LEAN_TARGET,
        "policy_classification_preserved": result_review.get("policy_classification")
        == POLICY_CLASSIFICATION
        and result_review.get("result_review_classification") == RESULT_REVIEW_CLASSIFICATION,
        "exact_lean_dependency_evidence_preserved": evidence.get("parsed_axioms")
        == EXPECTED_AXIOMS
        and evidence.get("exact_axioms_or_dependencies_used") == EXPECTED_AXIOMS
        and evidence.get("standard_lean_axioms_used") == EXPECTED_AXIOMS
        and decision.get("standard_lean_axioms_reviewed") == EXPECTED_AXIOMS,
        "project_axioms_used_empty": evidence.get("project_axioms_used")
        == PROJECT_AXIOMS_USED
        and evidence.get("project_axiom_count") == 0
        and decision.get("project_axioms_used") == PROJECT_AXIOMS_USED
        and decision.get("project_axiom_count") == 0,
        "documentation_markdown_records_required_scope": all(
            token in documentation_markdown
            for token in [
                SELECTED_REMEDIATION_FINDING_ID,
                SELECTED_DEPENDENCY,
                LEAN_TARGET,
                "propext",
                "Classical.choice",
                "Quot.sound",
                "project_axioms_used = []",
                "does not clear",
                "does not register blocker movement",
                TRANCHE_001_STATUS,
                TRANCHE_002_STATUS,
            ]
        ),
        "release_blockers_remain_tracked": _release_blockers_tracked(release_blockers),
        "other_three_obligations_carried_forward": _other_obligations_carried_forward(
            other_obligations
        ),
        "prepares_documentation_only": forbidden_effect_status[
            "documentation_execution_performed"
        ]
        is False,
        "does_not_clear_or_move_blocker": forbidden_effect_status[
            "blocker_fully_remediated"
        ]
        is False
        and forbidden_effect_status["blocker_movement_authorized"] is False
        and forbidden_effect_status["blocker_movement_registered"] is False,
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
        == "review_v01_alpha_dependency_remediation_tranche_003_documentation_packet_result",
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
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_DOCUMENTATION_PACKET_BLOCKED",
        "consumes_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_result_review_pointer": _ptr(result_review_path),
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "packet_scope": (
            "PREPARE_TRANCHE_003_DOCUMENTATION_PACKET_ONLY_NO_BLOCKER_CLEARANCE_OR_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_REMEDIATION_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "lean_audit_target": lean_target,
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
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "documentation_purpose": (
            "Record the standard Lean axiom posture for tranche 003 after policy adjudication "
            "accepted it with a documentation requirement."
        ),
        "documentation_scope": (
            "Selected finding V01-ALPHA-DEP-REM-003 and dependency "
            "finite_transport_theorems_construct_residual_package_v0 only."
        ),
        "documentation_surface": {
            "surface": _ptr(documentation_path),
            "kind": "policy_accepted_dependency_posture_documentation",
            "status": "prepared",
            "preparation_only": True,
        },
        "documentation_sections": [
            "selected finding and dependency",
            "accepted Lean dependencies",
            "project-local axioms absent",
            "standard Lean axiom acceptability rationale",
            "what this documentation does not prove",
            "blocker movement boundary",
            "tranche 001 and tranche 002 carry-forward",
            "other three blockers carried forward unchanged",
        ],
        "what_this_documentation_does_not_prove": [
            "It does not prove the selected dependency.",
            "It does not discharge Lean theorem debt or proof debt.",
            "It does not discharge retained assumptions.",
            "It does not clear or downgrade tranche 003 by itself.",
            "It does not register blocker movement for tranche 003.",
            "It does not assemble the release packet or mark v0.1-alpha readiness.",
            "It does not authorize Phase 2, seam closure, empirical validation, or master-action promotion.",
        ],
        "standard_lean_axiom_acceptability_rationale": decision.get("decision"),
        "project_local_axiom_absence_rationale": (
            "The accepted evidence records project_axioms_used = [] and project_axiom_count = 0."
        ),
        "blocker_movement_boundary": (
            "Tranche 003 remains blocking until documentation result review, later status "
            "adjudication, and separate movement registration authorize a status movement."
        ),
        "documentation_packet_prepared": accepted,
        "documentation_surface_prepared": accepted,
        "documentation_execution_performed": False,
        "documentation_result_review_required": True,
        "tranche_003_release_blocker_status": "still_blocking_pending_documentation_packet_result_review",
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_DOCUMENTATION_PACKET",
        "selected_next_target_kind": "documentation_packet_result_review_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_TRANCHE_003_DOCUMENTATION_PACKET_RESULT_ONLY_NO_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The prepared tranche 003 documentation packet must be reviewed before status adjudication or blocker movement can be considered.",
            },
            {
                "target": "prepare_v01_alpha_dependency_remediation_tranche_003_status_adjudication_packet",
                "decision": "deferred",
                "reason": "Status adjudication remains deferred until tranche 003 documentation is reviewed.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Release-readiness adjudication remains blocked by tranche 003 documentation result review and tracked blockers.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 003 documentation packet prepares a "
            "documentation surface for the policy-accepted standard Lean axiom posture only. It "
            "does not clear or move the blocker, discharge Lean theorem debt, reduce "
            "axiom/spec-backed proof debt, discharge retained assumptions, assemble the release "
            "packet, mark v0.1-alpha readiness, authorize Phase 2, close seams, validate "
            "empirically, promote the master action, promote claims, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    documentation_out: Path = DEFAULT_DOCUMENTATION_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    payload = build_packet(
        result_review_path=result_review_path,
        documentation_path=documentation_out,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    documentation_out.parent.mkdir(parents=True, exist_ok=True)
    documentation_out.write_text(build_documentation_markdown(result_review), encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the v0.1-alpha dependency remediation tranche 003 documentation packet."
    )
    parser.add_argument("--result-review", type=Path, default=DEFAULT_RESULT_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--documentation-out", type=Path, default=DEFAULT_DOCUMENTATION_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    result_review_path = (
        ns.result_review if ns.result_review.is_absolute() else (REPO_ROOT / ns.result_review)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    documentation_out = (
        ns.documentation_out
        if ns.documentation_out.is_absolute()
        else (REPO_ROOT / ns.documentation_out)
    )
    payload = write_packet(
        result_review_path=result_review_path,
        out=out,
        documentation_out=documentation_out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_dependency_remediation_tranche_003_documentation_packet_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} "
        f"out={_ptr(out)} documentation={_ptr(documentation_out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
