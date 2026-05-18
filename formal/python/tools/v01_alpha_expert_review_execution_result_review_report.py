from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_EXPERT_REVIEW_EXECUTION_RESULT_REVIEW_20260515_v0"
REVIEW_ID = "V01_ALPHA_EXPERT_REVIEW_EXECUTION_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "V01_ALPHA_EXPERT_REVIEW_EXECUTION_RESULT_REVIEW_ACCEPTS_REVIEW_EVIDENCE_"
    "AND_AUTHORIZES_DEPENDENCY_REMEDIATION_PACKET_PREPARATION_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_EXECUTION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_EXPERT_REVIEW_EXECUTION_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_EXPERT_REVIEW_EXECUTION_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_EXECUTION_ID = "V01_ALPHA_EXPERT_REVIEW_EXECUTION_v0"
EXPECTED_EXECUTION_OUTCOME = "V01_ALPHA_EXPERT_REVIEW_EXECUTED_AS_REVIEW_EVIDENCE_ONLY_WITH_NO_RELEASE_PROMOTION"
EXPECTED_EXECUTION_SCOPE = "BOUNDED_EXPERT_REVIEW_EXECUTION_ONLY_NO_RELEASE_PROMOTION"
EXPECTED_EXECUTION_SELECTED_TARGET = "review_v01_alpha_expert_review_execution_result"
NEXT_TARGET = "prepare_v01_alpha_dependency_remediation_packet"

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


def _findings(execution: dict[str, Any]) -> dict[str, Any]:
    return execution.get("review_findings", {})


def _release_blocking_findings(execution: dict[str, Any]) -> list[dict[str, Any]]:
    return list(_findings(execution).get("release_blocking_dependency_findings", []))


def _unresolved_blocker_findings(execution: dict[str, Any]) -> list[dict[str, Any]]:
    return list(_findings(execution).get("unresolved_theorem_seam_master_action_blocker_findings", []))


def _retained_assumptions_remain_retained(execution: dict[str, Any]) -> bool:
    retained = _findings(execution).get("retained_assumption_findings", {})
    return (
        retained.get("row_count") == 22
        and retained.get("remain_retained") is True
        and retained.get("discharged_by_this_execution_count") == 0
    )


def _review_evidence_complete(execution: dict[str, Any]) -> bool:
    summary = execution.get("finding_summary", {})
    findings = _findings(execution)
    return (
        summary.get("release_blocking_dependency_finding_count") == 6
        and summary.get("documentation_only_dependency_finding_count") == 3
        and summary.get("expert_review_required_dependency_finding_count") == 6
        and summary.get("retained_assumption_finding_count") == 22
        and summary.get("proof_debt_class_count") == 3
        and summary.get("lean_dependency_row_count") == 6
        and summary.get("unresolved_blocker_finding_count") == 6
        and len(findings.get("release_blocking_dependency_findings", [])) == 6
        and len(findings.get("documentation_only_dependency_findings", [])) == 3
        and len(findings.get("expert_review_required_dependency_findings", [])) == 6
        and len(findings.get("unresolved_theorem_seam_master_action_blocker_findings", [])) == 6
    )


def _remediation_required(execution: dict[str, Any]) -> bool:
    release_blocking = _release_blocking_findings(execution)
    unresolved = _unresolved_blocker_findings(execution)
    return (
        len(release_blocking) == 6
        and all(row.get("requires_remediation_before_release_assembly") is True for row in release_blocking)
        and len(unresolved) == 6
        and execution.get("finding_summary", {}).get("release_readiness_adjudication_pending") is True
    )


def build_result_review(
    *,
    execution_path: Path = DEFAULT_EXECUTION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    execution = _read_json(execution_path)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}
    findings = _findings(execution)
    summary = execution.get("finding_summary", {})
    remediation_required = _remediation_required(execution)

    acceptance_criteria = {
        "consumes_expert_review_execution": execution.get("execution_id") == EXPECTED_EXECUTION_ID,
        "execution_completed": execution.get("executed") is True,
        "execution_outcome_review_evidence_only": execution.get("outcome_id")
        == EXPECTED_EXECUTION_OUTCOME,
        "execution_scope_bounded": execution.get("execution_scope") == EXPECTED_EXECUTION_SCOPE,
        "execution_selected_this_review": execution.get("selected_next_target")
        == EXPECTED_EXECUTION_SELECTED_TARGET,
        "expert_review_output_is_evidence_only": execution.get("authorization_boundary", {}).get(
            "expert_review_output_is_evidence_only"
        )
        is True,
        "review_evidence_complete": _review_evidence_complete(execution),
        "actual_findings_summarized": all(
            key in findings
            for key in [
                "release_blocking_dependency_findings",
                "documentation_only_dependency_findings",
                "expert_review_required_dependency_findings",
                "retained_assumption_findings",
                "proof_debt_findings",
                "lean_dependency_findings",
                "axiom_spec_backed_ledger_findings",
                "unresolved_theorem_seam_master_action_blocker_findings",
            ]
        ),
        "release_blocking_dependency_findings_preserved": summary.get(
            "release_blocking_dependency_finding_count"
        )
        == 6,
        "documentation_only_dependency_findings_preserved": summary.get(
            "documentation_only_dependency_finding_count"
        )
        == 3,
        "expert_review_required_dependency_findings_preserved": summary.get(
            "expert_review_required_dependency_finding_count"
        )
        == 6,
        "retained_assumptions_remain_retained": _retained_assumptions_remain_retained(execution),
        "proof_debt_not_reduced_by_execution": findings.get("proof_debt_findings", {}).get(
            "proof_debt_reduced_by_this_execution"
        )
        is False,
        "lean_theorem_debt_not_discharged_by_execution": findings.get(
            "lean_dependency_findings", {}
        ).get("theorem_debt_discharged_by_this_execution")
        is False,
        "axiom_spec_backed_debt_not_reduced_by_execution": findings.get(
            "axiom_spec_backed_ledger_findings", {}
        ).get("axiom_spec_backed_debt_reduced_by_this_execution")
        is False,
        "remediation_required_before_release_assembly": remediation_required,
        "release_readiness_adjudication_deferred": remediation_required,
        "no_release_packet_assembly": forbidden_effect_status["release_packet_assembled"] is False,
        "no_v01_readiness_marking": forbidden_effect_status["v01_alpha_marked_ready"] is False,
        "no_lean_theorem_debt_discharge": forbidden_effect_status["lean_theorem_debt_discharged"]
        is False,
        "no_axiom_spec_backed_debt_reduction": forbidden_effect_status[
            "axiom_spec_backed_debt_reduced"
        ]
        is False,
        "no_retained_assumption_discharge": forbidden_effect_status["retained_assumptions_discharged"]
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
        == "prepare_v01_alpha_dependency_remediation_packet",
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
        else "V01_ALPHA_EXPERT_REVIEW_EXECUTION_RESULT_REVIEW_BLOCKED",
        "consumes_execution": EXPECTED_EXECUTION_ID,
        "consumes_execution_pointer": _ptr(execution_path),
        "consumed_execution_schema_id": execution.get("schema_id"),
        "source_execution_packet": execution.get("source_execution_packet"),
        "source_expert_review_packet": execution.get("source_expert_review_packet"),
        "review_scope": "EXPERT_REVIEW_EXECUTION_RESULT_REVIEW_ONLY_NO_RELEASE_PROMOTION",
        "review_acceptance_posture": "expert_review_evidence_accepted_with_dependency_remediation_required",
        "execution_outcome_reviewed": execution.get("outcome_id"),
        "review_evidence_summary": {
            "release_blocking_dependency_finding_count": summary.get(
                "release_blocking_dependency_finding_count"
            ),
            "documentation_only_dependency_finding_count": summary.get(
                "documentation_only_dependency_finding_count"
            ),
            "expert_review_required_dependency_finding_count": summary.get(
                "expert_review_required_dependency_finding_count"
            ),
            "retained_assumption_finding_count": summary.get("retained_assumption_finding_count"),
            "proof_debt_class_count": summary.get("proof_debt_class_count"),
            "lean_dependency_row_count": summary.get("lean_dependency_row_count"),
            "unresolved_blocker_finding_count": summary.get("unresolved_blocker_finding_count"),
            "release_promotion_recommended": summary.get("release_promotion_recommended"),
            "release_readiness_adjudication_pending": summary.get(
                "release_readiness_adjudication_pending"
            ),
        },
        "actual_findings_summary": {
            "release_blocking_dependencies": [
                {
                    "theorem": row.get("theorem"),
                    "blocks_v01_alpha_release_packet": row.get(
                        "blocks_v01_alpha_release_packet"
                    ),
                    "requires_remediation_before_release_assembly": row.get(
                        "requires_remediation_before_release_assembly"
                    ),
                    "proof_debt_discharge_claim": row.get("proof_debt_discharge_claim"),
                }
                for row in _release_blocking_findings(execution)
            ],
            "retained_assumptions": {
                "row_count": findings.get("retained_assumption_findings", {}).get("row_count"),
                "remain_retained": findings.get("retained_assumption_findings", {}).get(
                    "remain_retained"
                ),
                "discharged_by_execution_count": findings.get(
                    "retained_assumption_findings", {}
                ).get("discharged_by_this_execution_count"),
            },
            "proof_debt": {
                "class_count": findings.get("proof_debt_findings", {}).get("class_count"),
                "proof_debt_reduced_by_execution": findings.get("proof_debt_findings", {}).get(
                    "proof_debt_reduced_by_this_execution"
                ),
            },
            "lean_dependency": {
                "dependency_row_count": findings.get("lean_dependency_findings", {}).get(
                    "dependency_row_count"
                ),
                "theorem_debt_discharged_by_execution": findings.get(
                    "lean_dependency_findings", {}
                ).get("theorem_debt_discharged_by_this_execution"),
            },
            "axiom_spec_backed_ledger": {
                "retained_assumption_count": findings.get(
                    "axiom_spec_backed_ledger_findings", {}
                ).get("retained_assumption_count"),
                "spec_backed_count": findings.get("axiom_spec_backed_ledger_findings", {}).get(
                    "spec_backed_count"
                ),
                "debt_reduced_by_execution": findings.get(
                    "axiom_spec_backed_ledger_findings", {}
                ).get("axiom_spec_backed_debt_reduced_by_this_execution"),
            },
            "unresolved_blockers": [
                {
                    "dependency": row.get("dependency"),
                    "finding": row.get("finding"),
                    "promotion_effect": row.get("promotion_effect"),
                }
                for row in _unresolved_blocker_findings(execution)
            ],
        },
        "routing_decision": {
            "remediation_required_before_release_assembly": remediation_required,
            "release_readiness_adjudication_preparation_authorized": False,
            "dependency_remediation_packet_preparation_authorized": accepted,
            "reason": (
                "Expert-review evidence is accepted, but all six release-blocking dependency "
                "findings require remediation before release assembly and six unresolved blocker "
                "findings remain pending."
            ),
        },
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
        else "REMEDIATE_V01_ALPHA_EXPERT_REVIEW_EXECUTION_RESULT_REVIEW",
        "selected_next_target_kind": "dependency_remediation_packet_preparation_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": "PREPARE_DEPENDENCY_REMEDIATION_PACKET_ONLY_NO_RELEASE_PROMOTION",
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "Review evidence is accepted but release-blocking dependencies require remediation before release-readiness adjudication can be prepared.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Readiness adjudication preparation is deferred until dependency-remediation planning addresses the accepted expert-review blocker evidence.",
            },
            {
                "target": "assemble_v01_alpha_public_release_packet",
                "decision": "deferred",
                "reason": "Release assembly remains blocked by retained assumptions, proof-debt posture, and release-blocking dependency findings.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha expert review execution result review accepts bounded review evidence "
            "and authorizes only dependency-remediation packet preparation. It does not assemble the "
            "release packet, mark v0.1-alpha readiness, discharge Lean theorem debt, reduce "
            "axiom/spec-backed proof debt, discharge retained assumptions, authorize Phase 2, close "
            "seams, validate empirically, promote the master action, promote claims, or make an "
            "external-truth claim."
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
        description="Generate the v0.1-alpha expert review execution result review."
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
        "v01_alpha_expert_review_execution_result_review_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
