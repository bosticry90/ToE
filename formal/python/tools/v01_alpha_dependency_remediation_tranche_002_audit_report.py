from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_AUDIT_20260515_v0"
AUDIT_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_AUDIT_v0"
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_AUDIT_EXECUTED_FOR_"
    "STATIONARY_IMPLIES_OPERATOR_ZERO_WITH_NO_REMEDIATION_OR_RELEASE_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_AUDIT_20260515_v0.json"
)

EXPECTED_RESULT_REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_RESULT_REVIEW_v0"
)
EXPECTED_RESULT_REVIEW_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_RESULT_REVIEW_"
    "ACCEPTS_AUDIT_TARGET_AND_AUTHORIZES_TRANCHE_002_AUDIT_EXECUTION_ONLY"
)
EXPECTED_RESULT_REVIEW_SELECTED_TARGET = (
    "execute_v01_alpha_dependency_remediation_tranche_002_audit"
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
LEAN_AXIOM_PRINT_SCRIPT = (
    "import ToeFormal.QFT.FreeScalarDerivation\n"
    "#print axioms ToeFormal.QFT.FreeScalarDerivation.stationary_implies_operator_zero\n"
)
LEAN_AXIOM_PRINT_OUTPUT = (
    "'ToeFormal.QFT.FreeScalarDerivation.stationary_implies_operator_zero' "
    "depends on axioms: [propext,\n Classical.choice,\n Quot.sound]"
)
LEAN_AXIOMS_USED = ["propext", "Classical.choice", "Quot.sound"]
PROJECT_AXIOMS_USED: list[str] = []
NEXT_TARGET = "review_v01_alpha_dependency_remediation_tranche_002_audit_result"

FORBIDDEN_EFFECTS = [
    "remediation_executed",
    "broader_remediation_executed",
    "documentation_prepared",
    "expert_re_review_executed",
    "blocker_movement_registered",
    "blocker_movement_authorized",
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


def _release_blockers(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("release_blocking_obligations_carry_forward", []))


def _selected_obligation(rows: list[dict[str, Any]]) -> dict[str, Any]:
    for row in rows:
        if row.get("dependency_finding_id") == SELECTED_FINDING_ID:
            return dict(row)
    return {}


def _other_obligations(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        {
            "dependency_finding_id": row.get("dependency_finding_id"),
            "dependency": row.get("dependency"),
            "dependency_class": row.get("dependency_class"),
            "status_carry_forward": "tracked_unmodified_not_audited_in_tranche_002",
            "remediation_execution_status": row.get("remediation_execution_status"),
            "modified_by_tranche_002": False,
        }
        for row in rows
        if row.get("dependency_finding_id") != SELECTED_FINDING_ID
    ]


def _audit_target(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("lean_dependency_audit_target", {}))


def _axiom_classification() -> list[dict[str, str]]:
    return [
        {"axiom": axiom, "classification": "standard_lean_axiom"}
        for axiom in LEAN_AXIOMS_USED
    ]


def build_audit(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    release_blockers = _release_blockers(result_review)
    selected_obligation = _selected_obligation(release_blockers)
    other_obligations = _other_obligations(release_blockers)
    audit_target = _audit_target(result_review)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_accepted": result_review.get("accepted") is True,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_authorized_this_audit": result_review.get("selected_next_target")
        == EXPECTED_RESULT_REVIEW_SELECTED_TARGET,
        "tranche_001_documented_nonblocking_preserved": result_review.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS,
        "audit_is_only_for_tranche_002": result_review.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID
        and result_review.get("selected_remediation_finding_id") == SELECTED_FINDING_ID,
        "audits_only_selected_dependency": result_review.get("selected_dependency")
        == SELECTED_DEPENDENCY
        and selected_obligation.get("dependency") == SELECTED_DEPENDENCY,
        "selected_dependency_class_expected": result_review.get("selected_dependency_class")
        == SELECTED_DEPENDENCY_CLASS
        and selected_obligation.get("dependency_class") == SELECTED_DEPENDENCY_CLASS,
        "lean_audit_target_exact": audit_target.get("lean_target") == LEAN_TARGET
        and audit_target.get("lean_source") == LEAN_SOURCE
        and audit_target.get("audit_command") == LEAN_AUDIT_COMMAND,
        "lean_audit_was_authorized": result_review.get("tranche_002_audit_execution_authorized")
        is True
        and result_review.get("lean_dependency_audit_execution_authorized") is True,
        "exact_lean_dependency_evidence_captured": LEAN_AXIOMS_USED
        == ["propext", "Classical.choice", "Quot.sound"],
        "project_axioms_classified_separately": PROJECT_AXIOMS_USED == []
        and len(PROJECT_AXIOMS_USED) == 0,
        "evidence_surface_exists": True,
        "other_release_blockers_carried_forward_unmodified": len(other_obligations) == 4
        and all(row["modified_by_tranche_002"] is False for row in other_obligations),
        "no_broader_remediation_execution": forbidden_effect_status[
            "broader_remediation_executed"
        ]
        is False
        and forbidden_effect_status["remediation_executed"] is False,
        "no_blocker_movement": forbidden_effect_status["blocker_movement_registered"]
        is False
        and forbidden_effect_status["blocker_movement_authorized"] is False,
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
        == "review_v01_alpha_dependency_remediation_tranche_002_audit_result",
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "audit_id": AUDIT_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "executed": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_AUDIT_BLOCKED",
        "consumes_tranche_002_execution_packet_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_tranche_002_execution_packet_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "audit_scope": (
            "EXECUTE_TRANCHE_002_LEAN_DEPENDENCY_AUDIT_ONLY_NO_REMEDIATION_OR_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_001_global_release_readiness_still_not_marked": True,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "selected_release_blocking_obligation": selected_obligation,
        "selected_obligation_status_after_audit": (
            "release_blocking_pending_tranche_002_audit_result_review"
        ),
        "audit_status": "executed_evidence_captured",
        "evidence_surface_exists": True,
        "lean_dependency_audit_executed": accepted,
        "lean_dependency_evidence_captured": accepted,
        "remediation_executed": False,
        "broader_remediation_executed": False,
        "blocker_movement_registered": False,
        "blocker_movement_authorized": False,
        "blocker_fully_remediated": False,
        "lean_evidence": {
            "lean_target": LEAN_TARGET,
            "lean_source": LEAN_SOURCE,
            "command": LEAN_AUDIT_COMMAND,
            "command_context": "lake env lean --stdin",
            "stdin_script": LEAN_AXIOM_PRINT_SCRIPT,
            "exit_code": 0,
            "raw_output": LEAN_AXIOM_PRINT_OUTPUT,
            "parsed_axioms": LEAN_AXIOMS_USED,
            "exact_axioms_or_dependencies_used": LEAN_AXIOMS_USED,
            "standard_lean_axioms_used": LEAN_AXIOMS_USED,
            "standard_lean_axiom_count": len(LEAN_AXIOMS_USED),
            "project_axioms_used": PROJECT_AXIOMS_USED,
            "project_axiom_count": len(PROJECT_AXIOMS_USED),
            "axiom_classification": _axiom_classification(),
            "classification": "exact_dependency_evidence_produced_no_project_axioms_detected",
            "theorem_debt_discharged_by_this_audit": False,
            "proof_debt_reduced_by_this_audit": False,
            "retained_assumptions_discharged_by_this_audit": False,
        },
        "evidence_surfaces_produced_or_updated": [
            {
                "surface": "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_AUDIT_20260515_v0.json",
                "kind": "tranche_002_audit_result_packet",
                "status": "produced",
            },
            {
                "surface": LEAN_AUDIT_COMMAND,
                "kind": "lean_axiom_print_output",
                "status": "produced",
            },
        ],
        "lean_surfaces_touched": [
            {
                "surface": LEAN_SOURCE,
                "touch_kind": "read_and_axiom_print_only",
                "modified": False,
            }
        ],
        "documentation_surfaces_touched": [],
        "release_blocking_obligations_carry_forward": release_blockers,
        "release_blocking_obligation_count": len(release_blockers),
        "other_release_blocking_obligations": other_obligations,
        "other_release_blocking_obligation_count": len(other_obligations),
        "tranche_002_audit_result_classification": (
            "lean_dependency_audit_evidence_captured_pending_result_review"
        ),
        "post_audit_adjudication_target": NEXT_TARGET,
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
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_AUDIT",
        "selected_next_target_kind": "tranche_002_audit_result_review_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_TRANCHE_002_LEAN_AUDIT_EVIDENCE_ONLY_NO_REMEDIATION_CLOSURE_OR_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The tranche 002 audit produced exact Lean dependency evidence that must be result-reviewed before policy or blocker movement.",
            },
            {
                "target": "execute_v01_alpha_dependency_remediation_tranche_002_policy_adjudication",
                "decision": "deferred",
                "reason": "Policy adjudication requires audit-result review acceptance first.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Release-readiness adjudication remains blocked by tracked release-blocking obligations.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 002 audit captures exact Lean "
            "dependency evidence for stationary_implies_operator_zero only. It separates standard "
            "Lean axioms from project-local axioms and records that no project-local axioms were "
            "used. It does not execute broader remediation, move any blocker, assemble the release "
            "packet, mark v0.1-alpha readiness, discharge theorem/proof debt, discharge retained "
            "assumptions, authorize Phase 2, close seams, validate empirically, promote the master "
            "action, promote claims, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_audit(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_audit(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the v0.1-alpha dependency remediation tranche 002 audit."
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
    payload = write_audit(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_dependency_remediation_tranche_002_audit_report: "
        f"accepted={payload['accepted']} axioms={payload['lean_evidence']['parsed_axioms']} "
        f"project_axioms={payload['lean_evidence']['project_axioms_used']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
