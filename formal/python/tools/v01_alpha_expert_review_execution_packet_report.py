from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_20260515_v0"
PACKET_ID = "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_v0"
OUTCOME_ID = (
    "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_PREPARED_WITH_NO_EXPERT_REVIEW_"
    "EXECUTION_OR_RELEASE_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_EXPERT_REVIEW_PACKET_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_20260515_v0.json"
)

EXPECTED_RESULT_REVIEW_ID = "V01_ALPHA_EXPERT_REVIEW_PACKET_RESULT_REVIEW_v0"
EXPECTED_RESULT_REVIEW_OUTCOME = (
    "V01_ALPHA_EXPERT_REVIEW_PACKET_RESULT_REVIEW_ACCEPTS_REVIEW_SCOPE_ONLY_"
    "AND_AUTHORIZES_EXPERT_REVIEW_EXECUTION_PACKET_PREPARATION_ONLY"
)
EXPECTED_CONSUMED_TARGET = "prepare_v01_alpha_expert_review_execution_packet"
EXPECTED_RESULT_NEXT_ACTION_SCOPE = "PREPARE_EXECUTION_PACKET_ONLY_NO_EXPERT_REVIEW_EXECUTION"
EXPECTED_EXPERT_PACKET_ID = "V01_ALPHA_EXPERT_REVIEW_PACKET_v0"
EXPECTED_PACKET_GAP = "EXPERT_REVIEW_PACKET_PREPARED_BUT_REVIEW_NOT_EXECUTED_V0"
NEXT_TARGET = "review_v01_alpha_expert_review_execution_packet_result"

FORBIDDEN_EFFECTS = [
    "expert_review_executed",
    "expert_review_execution_authorized",
    "expert_review_conclusions_produced",
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

REQUIRED_EXECUTION_PACKET_SECTIONS = {
    "reviewer_inputs",
    "reviewer_questions",
    "review_scope_boundaries",
    "review_acceptance_criteria",
    "review_failure_criteria",
    "evidence_bundle_pointers",
    "lean_dependency_audit_posture_pointers",
    "axiom_spec_backed_ledger_pointers",
    "retained_assumption_review_expectations",
    "release_blocking_dependency_review_expectations",
    "expert_review_output_schema",
    "post_review_adjudication_rules",
}


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


def _dependency_rows_still_unexecuted(packet: dict[str, Any]) -> bool:
    rows = packet.get("dependency_review_rows", [])
    if len(rows) != 6:
        return False
    return all(
        row.get("review_execution_status") == "not_executed_v0"
        and row.get("reviewer_assessment_status") == "prepared_not_assessed"
        and row.get("proof_debt_discharge_claim") is False
        for row in rows
    )


def _retained_assumptions_remain_retained(packet: dict[str, Any]) -> bool:
    retained = packet.get("review_scope", {}).get("retained_assumptions", {})
    rows = retained.get("rows", [])
    return len(rows) == 22 and all(row.get("status") == "retained_assumption" for row in rows)


def _reviewer_inputs(
    *,
    result_review_path: Path,
    expert_packet_path: Path,
    capture_packet_path: Path,
    result_review: dict[str, Any],
    expert_packet: dict[str, Any],
    capture_packet: dict[str, Any],
) -> list[dict[str, Any]]:
    summary = result_review.get("packet_summary_reviewed", {})
    return [
        {
            "input_id": "expert_review_packet_result_review",
            "pointer": _ptr(result_review_path),
            "required": True,
            "expected_review_id": EXPECTED_RESULT_REVIEW_ID,
            "accepted": result_review.get("accepted") is True,
            "scope": result_review.get("review_scope"),
        },
        {
            "input_id": "expert_review_packet",
            "pointer": _ptr(expert_packet_path),
            "required": True,
            "expected_packet_id": EXPECTED_EXPERT_PACKET_ID,
            "prepared": expert_packet.get("prepared") is True,
            "review_execution_status": expert_packet.get("review_execution_status"),
        },
        {
            "input_id": "lean_dependency_audit_capture_packet",
            "pointer": _ptr(capture_packet_path),
            "required": True,
            "dependency_row_count": capture_packet.get("capture_summary", {}).get(
                "v01_dependency_audit_row_count"
            ),
            "primary_capture_gap": capture_packet.get("capture_summary", {}).get("primary_capture_gap"),
        },
        {
            "input_id": "dependency_review_rows",
            "pointer": f"{_ptr(expert_packet_path)}::dependency_review_rows",
            "required": True,
            "row_count": summary.get("dependency_review_row_count"),
            "expected_row_status": "not_executed_v0/prepared_not_assessed",
        },
        {
            "input_id": "retained_assumption_rows",
            "pointer": f"{_ptr(expert_packet_path)}::review_scope.retained_assumptions.rows",
            "required": True,
            "row_count": summary.get("retained_assumption_count"),
            "expected_status": "retained_assumption",
        },
    ]


def _reviewer_questions() -> list[str]:
    return [
        "Are all release-facing dependency rows correctly classified as release-blocking, documentation-only, or review-required?",
        "Do the Lean dependency-audit rows and #print axioms commands identify the exact dependency posture required for v0.1-alpha review?",
        "Which retained assumptions remain blockers for release packet assembly, theorem-debt discharge, seam closure, or master-action promotion?",
        "Does any dependency row require remediation before a later expert review execution can produce a valid conclusion?",
        "What evidence bundle is sufficient for a later result review to decide whether expert review execution may proceed?",
    ]


def _review_scope_boundaries() -> dict[str, Any]:
    return {
        "execution_wrapper_scope": "prepare_controlled_expert_review_execution_packet_only",
        "this_packet_executes_expert_review": False,
        "this_packet_authorizes_expert_review_execution": False,
        "this_packet_produces_review_conclusions": False,
        "in_scope": [
            "reviewer input manifest",
            "reviewer question set",
            "release-facing dependency review boundaries",
            "retained-assumption inspection expectations",
            "release-blocking dependency inspection expectations",
            "future expert-review output schema",
            "post-review adjudication routing rules",
        ],
        "out_of_scope": [
            "expert review execution",
            "review conclusions",
            "release packet assembly",
            "v0.1-alpha readiness marking",
            "Lean theorem debt discharge",
            "axiom/spec-backed proof debt reduction",
            "retained-assumption discharge",
            "Phase 2 authorization",
            "seam closure",
            "empirical validation",
            "master-action promotion",
            "claim promotion",
        ],
    }


def _review_acceptance_criteria() -> list[dict[str, Any]]:
    return [
        {
            "criterion_id": "inputs_complete",
            "requirement": "All required reviewer inputs and evidence bundle pointers are present and repository-local.",
            "release_effect": "none_by_this_packet",
        },
        {
            "criterion_id": "dependency_rows_classified",
            "requirement": "Each release-facing dependency row receives a classification and rationale in a later expert review output.",
            "release_effect": "classification_only_until_separate_adjudication",
        },
        {
            "criterion_id": "retained_assumptions_explicit",
            "requirement": "Retained assumptions are reviewed as retained and are not treated as discharged by review text.",
            "release_effect": "no_proof_debt_reduction",
        },
        {
            "criterion_id": "release_blockers_explicit",
            "requirement": "Release-blocking dependencies remain blocking unless a later separate proof/dependency adjudication authorizes otherwise.",
            "release_effect": "no_release_readiness_marking",
        },
        {
            "criterion_id": "forbidden_promotions_absent",
            "requirement": "The future expert-review output must not mark readiness, discharge theorem debt, close seams, or promote the master action.",
            "release_effect": "promotion_firewall_preserved",
        },
    ]


def _review_failure_criteria() -> list[dict[str, Any]]:
    return [
        {
            "criterion_id": "missing_required_input",
            "failure_condition": "Any required evidence pointer, dependency row, or retained-assumption row is missing.",
            "required_response": "block_or_remediate_before_execution",
        },
        {
            "criterion_id": "review_conclusion_without_execution",
            "failure_condition": "The packet or a later result review records expert-review conclusions before authorized execution.",
            "required_response": "invalidate_execution_packet_result",
        },
        {
            "criterion_id": "premature_debt_reduction",
            "failure_condition": "Any review text treats documentation, review, or packet preparation as theorem-debt or proof-debt discharge.",
            "required_response": "block_release_promotion",
        },
        {
            "criterion_id": "promotion_leak",
            "failure_condition": "Any Phase 2, seam-closure, empirical-validation, master-action-promotion, claim-promotion, or release-readiness flag is set true.",
            "required_response": "block_and_repair_packet",
        },
    ]


def _expert_review_output_schema() -> dict[str, Any]:
    return {
        "schema_id": "V01_ALPHA_EXPERT_REVIEW_OUTPUT_SCHEMA_v0",
        "schema_prepared": True,
        "output_produced_by_this_packet": False,
        "conclusions_produced_by_this_packet": False,
        "required_fields": [
            "review_id",
            "reviewer_role",
            "reviewed_input_bundle",
            "dependency_row_assessments",
            "retained_assumption_assessments",
            "release_blocking_dependency_assessments",
            "lean_dependency_audit_assessment",
            "axiom_spec_backed_ledger_assessment",
            "scope_boundary_attestation",
            "forbidden_promotion_attestation",
            "recommended_next_target",
        ],
        "dependency_row_assessment_required_fields": [
            "theorem",
            "source_file",
            "observed_dependency_result",
            "project_axioms_used",
            "supplied_structures_used",
            "release_dependency_class",
            "expert_reviewer_assessment",
            "blocks_v01_alpha_release_packet",
            "requires_remediation_before_release_assembly",
        ],
        "allowed_recommended_next_targets": [
            "execute_v01_alpha_expert_review_packet",
            "remediate_v01_alpha_expert_review_execution_packet",
            "hold_v01_alpha_release_readiness_chain",
        ],
        "forbidden_output_claims": [
            "release_ready",
            "theorem_debt_discharged",
            "proof_debt_reduced",
            "retained_assumptions_discharged",
            "phase2_authorized",
            "seam_closed",
            "empirical_validation_complete",
            "master_action_promoted",
            "claim_promoted",
        ],
    }


def _post_review_adjudication_rules() -> dict[str, Any]:
    return {
        "result_review_required_before_execution": True,
        "next_review_target": NEXT_TARGET,
        "execution_after_this_packet": "not_authorized",
        "execution_authorization_condition": (
            "Only review_v01_alpha_expert_review_execution_packet_result may later authorize "
            "execute_v01_alpha_expert_review_packet, and only within the packet schema."
        ),
        "review_output_effect": "expert_review_output_can_inform_later_adjudication_but_cannot_directly_promote_release",
        "release_readiness_effect": "none_by_this_packet",
        "debt_discharge_effect": "none_by_this_packet",
        "rules": [
            "A prepared execution packet must be result-reviewed before any expert review execution begins.",
            "Expert-review execution, if later authorized, may produce review findings but still cannot assemble the release packet by itself.",
            "Any release-readiness, theorem-debt, proof-debt, seam, Phase 2, empirical, master-action, or claim promotion requires a separate explicit adjudication artifact.",
        ],
    }


def _packet_sections(
    *,
    result_review_path: Path,
    expert_packet_path: Path,
    capture_packet_path: Path,
    result_review: dict[str, Any],
    expert_packet: dict[str, Any],
    capture_packet: dict[str, Any],
) -> dict[str, Any]:
    expert_scope = expert_packet.get("review_scope", {})
    capture_summary = capture_packet.get("capture_summary", {})
    return {
        "reviewer_inputs": _reviewer_inputs(
            result_review_path=result_review_path,
            expert_packet_path=expert_packet_path,
            capture_packet_path=capture_packet_path,
            result_review=result_review,
            expert_packet=expert_packet,
            capture_packet=capture_packet,
        ),
        "reviewer_questions": _reviewer_questions(),
        "review_scope_boundaries": _review_scope_boundaries(),
        "review_acceptance_criteria": _review_acceptance_criteria(),
        "review_failure_criteria": _review_failure_criteria(),
        "evidence_bundle_pointers": {
            "expert_review_packet_result_review": _ptr(result_review_path),
            "expert_review_packet": _ptr(expert_packet_path),
            "lean_dependency_audit_capture_packet": _ptr(capture_packet_path),
            "lean_dependency_audit_capture_result_review": expert_packet.get("consumes_result_review_pointer"),
            "lean_dependency_audit_table": capture_packet.get("lean_dependency_audit_pointer"),
            "lean_release_index": capture_packet.get("lean_release_index_pointer"),
            "lean_aggregate": capture_packet.get("lean_aggregate_pointer"),
            "axiom_spec_backed_ledger": capture_packet.get("axiom_spec_backed_ledger_pointer"),
            "axiom_refresh_result_review": capture_packet.get("axiom_refresh_result_review_pointer"),
        },
        "lean_dependency_audit_posture_pointers": {
            "dependency_audit_pointer": capture_packet.get("lean_dependency_audit_pointer"),
            "release_index_pointer": capture_packet.get("lean_release_index_pointer"),
            "release_index_command": capture_packet.get("current_lean_build_status", {}).get(
                "release_index_command"
            ),
            "release_index_status": capture_packet.get("current_lean_build_status", {}).get(
                "release_index_status"
            ),
            "dependency_row_count": capture_summary.get("v01_dependency_audit_row_count"),
            "release_index_check_count": capture_summary.get("release_index_check_count"),
            "relevant_module_count": capture_summary.get("relevant_module_count"),
            "primary_capture_gap": capture_summary.get("primary_capture_gap"),
        },
        "axiom_spec_backed_ledger_pointers": {
            "ledger_pointer": capture_packet.get("axiom_spec_backed_ledger_pointer"),
            "refresh_result_review_pointer": capture_packet.get("axiom_refresh_result_review_pointer"),
            "posture": capture_packet.get("axiom_ledger_posture", {}),
            "review_task": expert_scope.get("axiom_spec_backed_ledger_posture", {}).get("reviewer_task"),
        },
        "retained_assumption_review_expectations": {
            "row_count": expert_scope.get("retained_assumptions", {}).get("row_count"),
            "expected_status": "retained_assumption",
            "remain_retained_through_this_packet": True,
            "discharge_allowed_by_this_packet": False,
            "review_expectations": [
                "Confirm each retained-assumption row remains accurately labeled.",
                "Identify release-blocking retained assumptions without treating identification as discharge.",
                "Record remediation needs for later proof work or dependency adjudication.",
            ],
        },
        "release_blocking_dependency_review_expectations": {
            "row_count": expert_scope.get("release_blocking_dependencies", {}).get("row_count"),
            "dependency_names": expert_scope.get("release_blocking_dependencies", {}).get(
                "dependencies", []
            ),
            "expected_release_dependency_class": "release_blocking_pending_capture_or_review",
            "release_blocker_status_changes_allowed_by_this_packet": False,
            "review_expectations": [
                "Review each dependency against Lean audit posture and supplied-structure classification.",
                "Record whether the dependency remains release-blocking for v0.1-alpha packet assembly.",
                "Do not mark any dependency resolved, discharged, or release-ready in this packet.",
            ],
        },
        "expert_review_output_schema": _expert_review_output_schema(),
        "post_review_adjudication_rules": _post_review_adjudication_rules(),
    }


def build_execution_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    expert_packet_path = _resolve_repo_path(result_review.get("consumes_expert_review_packet_pointer"))
    expert_packet = _read_json(expert_packet_path)
    capture_packet_path = _resolve_repo_path(expert_packet.get("source_capture_packet_pointer"))
    capture_packet = _read_json(capture_packet_path)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}
    sections = _packet_sections(
        result_review_path=result_review_path,
        expert_packet_path=expert_packet_path,
        capture_packet_path=capture_packet_path,
        result_review=result_review,
        expert_packet=expert_packet,
        capture_packet=capture_packet,
    )
    packet_summary = result_review.get("packet_summary_reviewed", {})

    acceptance_criteria = {
        "consumes_expert_review_packet_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_pointer_matches": _ptr(result_review_path)
        == "formal/docs/release/V01_ALPHA_EXPERT_REVIEW_PACKET_RESULT_REVIEW_20260515_v0.json",
        "result_review_accepted": result_review.get("accepted") is True,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_selected_this_packet": result_review.get("selected_next_target")
        == EXPECTED_CONSUMED_TARGET,
        "result_review_scope_preparation_only": result_review.get("next_action_scope")
        == EXPECTED_RESULT_NEXT_ACTION_SCOPE,
        "source_expert_packet_matches": expert_packet.get("packet_id") == EXPECTED_EXPERT_PACKET_ID,
        "source_expert_packet_prepared": expert_packet.get("prepared") is True,
        "primary_packet_gap_preserved": packet_summary.get("primary_packet_gap") == EXPECTED_PACKET_GAP,
        "dependency_rows_preserved": packet_summary.get("dependency_review_row_count") == 6,
        "dependency_rows_still_unexecuted": _dependency_rows_still_unexecuted(expert_packet),
        "release_blocking_dependencies_preserved": packet_summary.get(
            "release_blocking_dependency_count"
        )
        == 6,
        "documentation_only_dependencies_preserved": packet_summary.get(
            "documentation_only_dependency_count"
        )
        == 3,
        "expert_review_required_dependencies_preserved": packet_summary.get(
            "expert_review_required_dependency_count"
        )
        == 6,
        "retained_assumptions_remain_retained": _retained_assumptions_remain_retained(expert_packet),
        "retained_assumption_count_preserved": packet_summary.get("retained_assumption_count") == 22,
        "proof_debt_class_count_preserved": packet_summary.get("proof_debt_class_count") == 3,
        "execution_packet_sections_present": set(sections) == REQUIRED_EXECUTION_PACKET_SECTIONS,
        "execution_schema_defined": sections["expert_review_output_schema"].get("schema_prepared")
        is True,
        "review_conclusions_not_produced": sections["expert_review_output_schema"].get(
            "conclusions_produced_by_this_packet"
        )
        is False,
        "no_expert_review_execution": forbidden_effect_status["expert_review_executed"] is False,
        "no_expert_review_execution_authorization": forbidden_effect_status[
            "expert_review_execution_authorized"
        ]
        is False,
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
        == "review_v01_alpha_expert_review_execution_packet_result",
    }
    prepared = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "classification": "P-POLICY/nonclaim",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_BLOCKED",
        "consumed_target": EXPECTED_CONSUMED_TARGET,
        "consumes_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_result_review_pointer": _ptr(result_review_path),
        "source_expert_review_packet": EXPECTED_EXPERT_PACKET_ID,
        "source_expert_review_packet_pointer": _ptr(expert_packet_path),
        "source_lean_dependency_audit_capture_packet": expert_packet.get("source_capture_packet"),
        "source_lean_dependency_audit_capture_packet_pointer": _ptr(capture_packet_path),
        "packet_scope": "PREPARE_EXPERT_REVIEW_EXECUTION_PACKET_ONLY_NO_REVIEW_EXECUTION_OR_RELEASE_PROMOTION",
        "execution_status": "not_executed_v0",
        "expert_review_executed": False,
        "expert_review_execution_authorized": False,
        "expert_review_conclusions_produced": False,
        "review_conclusions": {
            "produced": False,
            "items": [],
            "reason": "execution_packet_preparation_only",
        },
        "release_packet_assembled": False,
        "v01_alpha_marked_ready": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "axiom_spec_backed_debt_reduced_by_documentation": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "validation_claim_authorized": False,
        "packet_summary": {
            "primary_packet_gap": packet_summary.get("primary_packet_gap"),
            "dependency_review_row_count": packet_summary.get("dependency_review_row_count"),
            "release_blocking_dependency_count": packet_summary.get(
                "release_blocking_dependency_count"
            ),
            "documentation_only_dependency_count": packet_summary.get(
                "documentation_only_dependency_count"
            ),
            "expert_review_required_dependency_count": packet_summary.get(
                "expert_review_required_dependency_count"
            ),
            "retained_assumption_count": packet_summary.get("retained_assumption_count"),
            "proof_debt_class_count": packet_summary.get("proof_debt_class_count"),
            "execution_schema_defined": True,
            "review_conclusions_produced": False,
        },
        "execution_packet": sections,
        "forbidden_effect_status": forbidden_effect_status,
        "selected_next_target": NEXT_TARGET if prepared else "REMEDIATE_V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET",
        "selected_next_target_kind": "result_review_only",
        "selection_count": 1 if prepared else 0,
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The prepared execution wrapper must be reviewed before any expert review execution is authorized.",
            },
            {
                "target": "execute_v01_alpha_expert_review_packet",
                "decision": "deferred",
                "reason": "Execution remains closed until the execution-packet result review explicitly authorizes it.",
            },
            {
                "target": "assemble_v01_alpha_public_release_packet",
                "decision": "deferred",
                "reason": "Release assembly remains blocked while expert review execution and dependency adjudication are incomplete.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha expert review execution packet prepares a controlled execution wrapper only. "
            "It does not execute expert review, produce review conclusions, assemble the release packet, "
            "mark v0.1-alpha readiness, discharge Lean theorem debt, reduce axiom/spec-backed proof debt, "
            "discharge retained assumptions, authorize Phase 2, close seams, validate empirically, promote "
            "the master action, promote claims, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_execution_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_execution_packet(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the v0.1-alpha expert review execution packet."
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
    payload = write_execution_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_expert_review_execution_packet_report: "
        f"prepared={payload['prepared']} selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
