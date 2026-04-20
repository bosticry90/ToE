from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "RESEARCH_MODE_QM_STAT_SANDBOX_GOVERNED_INTAKE_EXECUTION_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "RESEARCH_MODE_QM_STAT_SANDBOX_GOVERNED_INTAKE_EXECUTION_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "research_mode_qm_stat_sandbox_governed_intake_execution_20260419_v0.json"
)


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read_text(path))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    execution_policy = dict(declaration.get("execution_policy", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))

    wrapper_report_path = REPO_ROOT / str(required_inputs.get("governed_review_wrapper_report", "")).strip()
    payload_record_path = REPO_ROOT / str(required_inputs.get("payload_record", "")).strip()
    comparison_report_path = REPO_ROOT / str(required_inputs.get("comparison_report", "")).strip()
    witness_binding_path = REPO_ROOT / str(required_inputs.get("witness_binding", "")).strip()
    promotion_lane_policy_path = REPO_ROOT / str(required_inputs.get("promotion_lane_policy", "")).strip()
    payload_requirements_path = REPO_ROOT / str(required_inputs.get("payload_requirements", "")).strip()

    wrapper_report = _read_json(wrapper_report_path)
    payload_record = _read_json(payload_record_path)
    comparison_report = _read_json(comparison_report_path)
    witness_binding = _read_json(witness_binding_path)
    promotion_lane_policy_text = _read_text(promotion_lane_policy_path)
    payload_requirements_text = _read_text(payload_requirements_path)

    wrapper_summary = dict(wrapper_report.get("summary", {}))
    wrapper_criteria = dict(wrapper_report.get("criteria", {}))
    payload_summary = dict(payload_record.get("summary", {}))
    payload_binding = dict(payload_record.get("target_binding", {}))
    comparison_summary = dict(comparison_report.get("summary", {}))
    comparison_record = dict(comparison_report.get("comparison_record", {}))
    harder_target = dict(comparison_record.get("harder_target", {}))

    promotion_policy_ok = all(
        token in promotion_lane_policy_text
        for token in (
            "PROMOTION_GOVERNANCE_LANE_HARD_BOUNDARY_v0: NO_CANONICAL_PROMOTION_WITHOUT_PROMOTION_REVIEW",
            "PROMOTION_GOVERNANCE_LANE_PROMOTION_RULE_v0: CANONICAL_ROW_AND_SEAM_STATE_CHANGE_ONLY_AFTER_GOVERNED_PROMOTION_PASS",
        )
    )
    payload_requirements_ok = all(
        token in payload_requirements_text
        for token in (
            "SANDBOX_PROMOTION_PAYLOAD_REQUIRED_FIELDS_v0: ARTIFACT_POINTER_PLUS_METADATA_RECORD_PLUS_TARGET_BINDING_PLUS_CONTRADICTION_CHECK_RESULT_PLUS_GOVERNED_TEST_SELECTION_PLUS_MUTATION_PLAN_PLUS_DECISION_BOUNDARY",
            "SANDBOX_PROMOTION_PAYLOAD_DECISION_SET_v0: PROMOTE_PLUS_HOLD_PLUS_REJECT_ONLY",
        )
    )
    wrapper_ready = (
        wrapper_summary.get("terminal_outcome")
        == str(execution_policy.get("required_wrapper_terminal_outcome", "")).strip()
        and wrapper_summary.get("governed_decision")
        == str(execution_policy.get("required_wrapper_decision", "")).strip()
        and wrapper_summary.get("canonical_mutation_emitted") is False
        and wrapper_criteria.get("payload_is_primary_object") is True
        and wrapper_criteria.get("comparison_surface_aligned") is True
    )
    bundle_binding_ok = (
        payload_binding.get("row_id") == str(execution_policy.get("required_target_row", "")).strip()
        and payload_binding.get("seam_id") == str(execution_policy.get("required_target_seam", "")).strip()
        and payload_binding.get("target_package_id") == str(execution_policy.get("required_target_package_id", "")).strip()
        and payload_binding.get("row_id") == witness_binding.get("row_id")
        and payload_binding.get("target_package_id") == witness_binding.get("target_package_id")
        and comparison_summary.get("row_id") == payload_binding.get("row_id")
        and comparison_summary.get("seam_id") == payload_binding.get("seam_id")
        and comparison_summary.get("target_package_id") == payload_binding.get("target_package_id")
    )
    support_role_ok = (
        comparison_record.get("comparison_disposition_v0")
        == "PAYLOAD_REMAINS_PRIMARY_GOVERNED_ENTRY_OBJECT_HARDER_TARGET_REMAINS_BOUND_SUPPORTING_EVIDENCE"
        and harder_target.get("promotability") == "NOT_READY"
    )
    intake_inputs_complete = all([promotion_policy_ok, payload_requirements_ok, wrapper_ready, bundle_binding_ok])

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "QM_STAT_SANDBOX_GOVERNED_INTAKE_HELD_PENDING_ADDED_SUPPORT")
    ).strip()

    if not intake_inputs_complete:
        terminal_outcome = "QM_STAT_SANDBOX_GOVERNED_INTAKE_REJECTED_DUE_TO_MISMATCH_OR_INSUFFICIENCY"
        intake_decision = "intake_rejected_due_to_mismatch_or_insufficiency"
        next_action = str(execution_policy.get("required_next_action_on_reject", "")).strip()
    elif not support_role_ok:
        terminal_outcome = "QM_STAT_SANDBOX_GOVERNED_INTAKE_HELD_PENDING_ADDED_SUPPORT"
        intake_decision = "intake_held_pending_added_support"
        next_action = str(execution_policy.get("required_next_action_on_hold", "")).strip()
    else:
        terminal_outcome = "QM_STAT_SANDBOX_GOVERNED_INTAKE_ACCEPTED_FOR_BOUNDED_SANDBOX_REVIEW"
        intake_decision = "intake_accepted_for_bounded_sandbox_review"
        next_action = str(execution_policy.get("required_next_action_on_accept", "")).strip()

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "promotion_policy_tokens_present": promotion_policy_ok,
            "payload_requirement_tokens_present": payload_requirements_ok,
            "wrapper_ready_for_intake": wrapper_ready,
            "bundle_binding_matches_live_anchor": bundle_binding_ok,
            "harder_target_preserved_as_support_only": support_role_ok,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_QM_STAT_SANDBOX_GOVERNED_INTAKE_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_QM_STAT_SANDBOX_GOVERNED_INTAKE_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "payload_primary_object_preserved": wrapper_summary.get("primary_artifact_id") == payload_summary.get("artifact_id"),
                "canonical_mutation_still_withheld": wrapper_summary.get("canonical_mutation_emitted") is False,
                "noncanonical_posture_preserved": wrapper_summary.get("canonical_status_v0")
                == "NONCANONICAL_UNLESS_EXPLICIT_GOVERNED_PROMOTION_PASS",
            },
            "inputs": {
                "wrapper_terminal_outcome": wrapper_summary.get("terminal_outcome"),
                "wrapper_decision": wrapper_summary.get("governed_decision"),
                "payload_artifact_id": payload_summary.get("artifact_id"),
                "payload_artifact_pointer": payload_summary.get("artifact_pointer"),
                "supporting_artifact_id": harder_target.get("artifact_id"),
                "row_id": payload_binding.get("row_id"),
                "seam_id": payload_binding.get("seam_id"),
                "target_package_id": payload_binding.get("target_package_id"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "intake_decision": intake_decision,
            "target_row_id": payload_binding.get("row_id"),
            "target_seam_id": payload_binding.get("seam_id"),
            "target_package_id": payload_binding.get("target_package_id"),
            "primary_artifact_id": payload_summary.get("artifact_id"),
            "supporting_artifact_id": harder_target.get("artifact_id"),
            "canonical_mutation_emitted": False,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "governed_review_wrapper_report": _ptr(wrapper_report_path),
            "payload_record": _ptr(payload_record_path),
            "comparison_report": _ptr(comparison_report_path),
            "witness_binding": _ptr(witness_binding_path),
            "promotion_lane_policy": _ptr(promotion_lane_policy_path),
            "payload_requirements": _ptr(payload_requirements_path),
        },
        "non_claim_boundary": "Repository-local sandbox governed-intake execution only; no governed promotion pass, canonical mutation, or seam-closure claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT sandbox governed-intake execution report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(declaration_path=declaration_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "research_mode_qm_stat_sandbox_governed_intake_execution_report: "
        f"decision={payload['summary']['intake_decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())