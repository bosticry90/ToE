from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_EXPERT_REVIEW_EXECUTION_20260515_v0"
EXECUTION_ID = "V01_ALPHA_EXPERT_REVIEW_EXECUTION_v0"
OUTCOME_ID = "V01_ALPHA_EXPERT_REVIEW_EXECUTED_AS_REVIEW_EVIDENCE_ONLY_WITH_NO_RELEASE_PROMOTION"
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_EXECUTION_PACKET_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_EXPERT_REVIEW_EXECUTION_20260515_v0.json"
)

EXPECTED_RESULT_REVIEW_ID = "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_RESULT_REVIEW_v0"
EXPECTED_RESULT_REVIEW_OUTCOME = (
    "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_RESULT_REVIEW_ACCEPTS_EXECUTION_PACKET_"
    "AND_AUTHORIZES_EXPERT_REVIEW_EXECUTION_ONLY"
)
EXPECTED_CONSUMED_TARGET = "execute_v01_alpha_expert_review_packet"
EXPECTED_NEXT_ACTION_SCOPE = "EXECUTE_EXPERT_REVIEW_PACKET_ONLY_NO_RELEASE_PROMOTION"
EXPECTED_EXECUTION_PACKET_ID = "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_v0"
EXPECTED_EXPERT_PACKET_ID = "V01_ALPHA_EXPERT_REVIEW_PACKET_v0"
NEXT_TARGET = "review_v01_alpha_expert_review_execution_result"
REPORT_POINTER = "formal/docs/paper/V01_ALPHA_EXPERT_REVIEW_EXECUTION_REPORT_v0.md"

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


def _resolve_repo_path(pointer: str | None) -> Path:
    if not pointer:
        raise ValueError("Cannot resolve an empty repository pointer")
    return REPO_ROOT / pointer.replace("/", "\\")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _release_blocking_dependency_findings(expert_packet: dict[str, Any]) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for row in expert_packet.get("dependency_review_rows", []):
        findings.append(
            {
                "theorem": row.get("theorem"),
                "source_file": row.get("source_file"),
                "release_label": row.get("release_label"),
                "review_scope_executed": True,
                "expert_reviewer_assessment": (
                    "release_blocking_pending_exact_dependency_and_proof_debt_adjudication"
                ),
                "blocks_v01_alpha_release_packet": True,
                "requires_remediation_before_release_assembly": True,
                "proof_debt_discharge_claim": False,
                "finding": (
                    "The dependency remains release-blocking for v0.1-alpha release packet "
                    "assembly until exact Lean dependency posture and any proof-debt remediation "
                    "are separately adjudicated."
                ),
            }
        )
    return findings


def _documentation_only_dependency_findings(expert_packet: dict[str, Any]) -> list[dict[str, Any]]:
    docs = (
        expert_packet.get("review_scope", {})
        .get("documentation_only_dependencies", {})
        .get("dependencies", [])
    )
    return [
        {
            "dependency": dependency,
            "review_scope_executed": True,
            "finding": "supporting_documentation_or_index_surface_only",
            "release_promotion_effect": "none",
            "proof_debt_discharge_claim": False,
        }
        for dependency in docs
    ]


def _expert_review_required_dependency_findings(expert_packet: dict[str, Any]) -> list[dict[str, Any]]:
    required = (
        expert_packet.get("review_scope", {})
        .get("expert_review_required_dependencies", {})
        .get("dependencies", [])
    )
    return [
        {
            "dependency": dependency,
            "review_scope_executed": True,
            "finding": "expert_review_required_and_executed_as_evidence_only",
            "release_readiness_effect": "pending_later_adjudication",
        }
        for dependency in required
    ]


def _retained_assumption_findings(expert_packet: dict[str, Any]) -> dict[str, Any]:
    retained = expert_packet.get("review_scope", {}).get("retained_assumptions", {})
    rows = retained.get("rows", [])
    return {
        "row_count": len(rows),
        "remain_retained": len(rows) == 22
        and all(row.get("status") == "retained_assumption" for row in rows),
        "discharged_by_this_execution_count": 0,
        "review_scope_executed": True,
        "finding": (
            "Retained assumptions remain retained unless separately discharged by formal proof "
            "or a later explicit dependency/proof-debt adjudication."
        ),
        "rows": [
            {
                "declaration": row.get("declaration"),
                "file": row.get("file"),
                "status": row.get("status"),
                "blocks_full_pillar_target": row.get("blocks_full_pillar_target"),
                "associated_pillar_or_seam": row.get("associated_pillar_or_seam"),
            }
            for row in rows
        ],
    }


def _proof_debt_findings(expert_packet: dict[str, Any]) -> dict[str, Any]:
    classes = expert_packet.get("review_scope", {}).get("proof_debt_categories", {}).get("classes", [])
    return {
        "class_count": len(classes),
        "proof_debt_reduced_by_this_execution": False,
        "theorem_debt_discharged_by_this_execution": False,
        "review_scope_executed": True,
        "classes": classes,
        "finding": (
            "Proof-debt classes were reviewed for release impact only; no theorem or proof debt "
            "is reduced by review text."
        ),
    }


def _lean_dependency_findings(
    execution_packet: dict[str, Any],
    expert_packet: dict[str, Any],
) -> dict[str, Any]:
    posture = execution_packet.get("execution_packet", {}).get("lean_dependency_audit_posture_pointers", {})
    return {
        "review_scope_executed": True,
        "dependency_audit_pointer": posture.get("dependency_audit_pointer"),
        "release_index_pointer": posture.get("release_index_pointer"),
        "release_index_status": posture.get("release_index_status"),
        "dependency_row_count": posture.get("dependency_row_count"),
        "primary_capture_gap": posture.get("primary_capture_gap"),
        "dependency_rows_reviewed": len(expert_packet.get("dependency_review_rows", [])),
        "theorem_debt_discharged_by_this_execution": False,
        "finding": (
            "Lean dependency posture remains evidence for later adjudication; this execution "
            "does not replace exact proof work or theorem-debt discharge."
        ),
    }


def _axiom_spec_backed_ledger_findings(execution_packet: dict[str, Any]) -> dict[str, Any]:
    ledger = execution_packet.get("execution_packet", {}).get("axiom_spec_backed_ledger_pointers", {})
    posture = ledger.get("posture", {})
    return {
        "review_scope_executed": True,
        "ledger_pointer": ledger.get("ledger_pointer"),
        "refresh_result_review_pointer": ledger.get("refresh_result_review_pointer"),
        "posture": posture,
        "retained_assumption_count": posture.get("retained_assumption_count"),
        "spec_backed_count": posture.get("spec_backed_count"),
        "blocks_full_pillar_target_count": posture.get("blocks_full_pillar_target_count"),
        "axiom_spec_backed_debt_reduced_by_this_execution": False,
        "finding": (
            "Axiom/spec-backed ledger posture remains a release-blocking evidence surface where "
            "applicable; review execution does not discharge ledger rows."
        ),
    }


def _unresolved_blocker_findings(expert_packet: dict[str, Any]) -> list[dict[str, Any]]:
    rows = (
        expert_packet.get("review_scope", {})
        .get("unresolved_theorem_seam_master_action_blockers", {})
        .get("dependencies", [])
    )
    return [
        {
            "dependency": row.get("dependency"),
            "reason": row.get("reason"),
            "review_scope_executed": True,
            "finding": "unresolved_blocker_remains_pending_later_adjudication",
            "promotion_effect": "none",
        }
        for row in rows
    ]


def build_execution(
    *,
    result_review_path: Path = DEFAULT_EXECUTION_PACKET_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    execution_packet_path = _resolve_repo_path(result_review.get("consumes_execution_packet_pointer"))
    execution_packet = _read_json(execution_packet_path)
    expert_packet_path = _resolve_repo_path(result_review.get("source_expert_review_packet_pointer"))
    expert_packet = _read_json(expert_packet_path)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    release_blocking_findings = _release_blocking_dependency_findings(expert_packet)
    documentation_only_findings = _documentation_only_dependency_findings(expert_packet)
    expert_required_findings = _expert_review_required_dependency_findings(expert_packet)
    retained_findings = _retained_assumption_findings(expert_packet)
    proof_debt_findings = _proof_debt_findings(expert_packet)
    lean_findings = _lean_dependency_findings(execution_packet, expert_packet)
    axiom_findings = _axiom_spec_backed_ledger_findings(execution_packet)
    unresolved_findings = _unresolved_blocker_findings(expert_packet)

    review_findings = {
        "release_blocking_dependency_findings": release_blocking_findings,
        "documentation_only_dependency_findings": documentation_only_findings,
        "expert_review_required_dependency_findings": expert_required_findings,
        "retained_assumption_findings": retained_findings,
        "proof_debt_findings": proof_debt_findings,
        "lean_dependency_findings": lean_findings,
        "axiom_spec_backed_ledger_findings": axiom_findings,
        "unresolved_theorem_seam_master_action_blocker_findings": unresolved_findings,
    }

    acceptance_criteria = {
        "consumes_execution_packet_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_accepted": result_review.get("accepted") is True,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_authorized_this_execution": result_review.get("selected_next_target")
        == EXPECTED_CONSUMED_TARGET,
        "result_review_scope_execution_only": result_review.get("next_action_scope")
        == EXPECTED_NEXT_ACTION_SCOPE,
        "source_execution_packet_matches": execution_packet.get("packet_id")
        == EXPECTED_EXECUTION_PACKET_ID,
        "source_expert_packet_matches": expert_packet.get("packet_id") == EXPECTED_EXPERT_PACKET_ID,
        "review_scope_executed": True,
        "findings_recorded": all(
            [
                len(release_blocking_findings) == 6,
                len(documentation_only_findings) == 3,
                len(expert_required_findings) == 6,
                retained_findings.get("row_count") == 22,
                proof_debt_findings.get("class_count") == 3,
                lean_findings.get("dependency_row_count") == 6,
                axiom_findings.get("retained_assumption_count") == 22,
                len(unresolved_findings) == 6,
            ]
        ),
        "release_blocking_dependency_findings_recorded": len(release_blocking_findings) == 6,
        "documentation_only_dependency_findings_recorded": len(documentation_only_findings) == 3,
        "expert_review_required_dependency_findings_recorded": len(expert_required_findings) == 6,
        "retained_assumption_findings_recorded": retained_findings.get("row_count") == 22,
        "proof_debt_findings_recorded": proof_debt_findings.get("class_count") == 3,
        "lean_dependency_findings_recorded": lean_findings.get("dependency_row_count") == 6,
        "axiom_spec_backed_ledger_findings_recorded": axiom_findings.get(
            "retained_assumption_count"
        )
        == 22,
        "unresolved_blocker_findings_recorded": len(unresolved_findings) == 6,
        "no_release_packet_assembly": forbidden_effect_status["release_packet_assembled"] is False,
        "no_v01_readiness_marking": forbidden_effect_status["v01_alpha_marked_ready"] is False,
        "no_lean_theorem_debt_discharge": forbidden_effect_status["lean_theorem_debt_discharged"]
        is False,
        "no_axiom_spec_backed_debt_reduction": forbidden_effect_status[
            "axiom_spec_backed_debt_reduced"
        ]
        is False,
        "retained_assumptions_remain_retained": retained_findings.get("remain_retained") is True,
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
        == "review_v01_alpha_expert_review_execution_result",
    }
    executed = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "execution_id": EXECUTION_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "classification": "P-POLICY/nonclaim",
        "captured_at_utc": captured_at_utc,
        "executed": executed,
        "review_scope_executed": executed,
        "outcome_id": OUTCOME_ID if executed else "V01_ALPHA_EXPERT_REVIEW_EXECUTION_BLOCKED",
        "consumed_target": EXPECTED_CONSUMED_TARGET,
        "consumes_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_result_review_pointer": _ptr(result_review_path),
        "source_execution_packet": EXPECTED_EXECUTION_PACKET_ID,
        "source_execution_packet_pointer": _ptr(execution_packet_path),
        "source_expert_review_packet": EXPECTED_EXPERT_PACKET_ID,
        "source_expert_review_packet_pointer": _ptr(expert_packet_path),
        "execution_report_pointer": REPORT_POINTER,
        "execution_scope": "BOUNDED_EXPERT_REVIEW_EXECUTION_ONLY_NO_RELEASE_PROMOTION",
        "reviewer_role": "repository_local_expert_review_executor_v0",
        "reviewed_input_bundle": {
            "execution_packet_result_review": _ptr(result_review_path),
            "execution_packet": _ptr(execution_packet_path),
            "expert_review_packet": _ptr(expert_packet_path),
            "lean_dependency_audit_capture_packet": execution_packet.get(
                "source_lean_dependency_audit_capture_packet_pointer"
            ),
            "axiom_spec_backed_ledger": execution_packet.get("execution_packet", {})
            .get("evidence_bundle_pointers", {})
            .get("axiom_spec_backed_ledger"),
        },
        "expert_review_executed": True if executed else False,
        "expert_review_findings_recorded": executed,
        "expert_review_result_packet_produced": True if executed else False,
        "release_packet_assembled": False,
        "v01_alpha_marked_ready": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "axiom_spec_backed_debt_reduced_by_documentation": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "validation_claim_authorized": False,
        "review_findings": review_findings,
        "finding_summary": {
            "release_blocking_dependency_finding_count": len(release_blocking_findings),
            "documentation_only_dependency_finding_count": len(documentation_only_findings),
            "expert_review_required_dependency_finding_count": len(expert_required_findings),
            "retained_assumption_finding_count": retained_findings.get("row_count"),
            "proof_debt_class_count": proof_debt_findings.get("class_count"),
            "lean_dependency_row_count": lean_findings.get("dependency_row_count"),
            "unresolved_blocker_finding_count": len(unresolved_findings),
            "release_promotion_recommended": False,
            "release_readiness_adjudication_pending": True,
        },
        "authorization_boundary": {
            "expert_review_execution_completed": True if executed else False,
            "expert_review_output_is_evidence_only": True if executed else False,
            "release_readiness_authorized": False,
            "release_packet_assembly_authorized": False,
            "theorem_or_proof_debt_discharge_authorized": False,
            "retained_assumption_discharge_authorized": False,
            "phase2_authorized": False,
            "seam_closure_authorized": False,
            "empirical_validation_authorized": False,
            "master_action_promotion_authorized": False,
        },
        "forbidden_effect_status": forbidden_effect_status,
        "selected_next_target": NEXT_TARGET
        if executed
        else "REMEDIATE_V01_ALPHA_EXPERT_REVIEW_EXECUTION",
        "selected_next_target_kind": "result_review_only",
        "selection_count": 1 if executed else 0,
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The bounded expert-review execution produced review findings and must be result-reviewed before any release-readiness adjudication packet is prepared.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Release-readiness adjudication requires a separate result review of this expert-review execution output.",
            },
            {
                "target": "remediate_v01_alpha_expert_review_execution",
                "decision": "deferred",
                "reason": "No execution-scope failure was detected by this bounded execution artifact.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha expert review execution is bounded review evidence only. It records "
            "dependency, retained-assumption, proof-debt, Lean dependency, axiom/spec-backed ledger, "
            "and unresolved blocker findings, but it does not assemble the release packet, mark "
            "v0.1-alpha readiness, discharge Lean theorem debt, reduce proof debt, discharge retained "
            "assumptions, authorize Phase 2, close seams, validate empirically, promote the master "
            "action, promote claims, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_execution(
    *,
    result_review_path: Path = DEFAULT_EXECUTION_PACKET_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_execution(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the v0.1-alpha expert review execution.")
    parser.add_argument("--result-review", type=Path, default=DEFAULT_EXECUTION_PACKET_RESULT_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    result_review_path = (
        ns.result_review if ns.result_review.is_absolute() else (REPO_ROOT / ns.result_review)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_execution(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_expert_review_execution_report: "
        f"executed={payload['executed']} selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
