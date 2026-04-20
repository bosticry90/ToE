from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_REPORT_20260414_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_20260414_v0.json"
)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _maybe_text(raw: Any) -> str:
    return str(raw).strip() if raw is not None else ""


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("policy_standard_approval_record_policy", {}))
    contract = dict(declaration.get("policy_standard_approval_record_contract", {}))

    approval_criteria_path = REPO_ROOT / str(
        required_inputs.get("bridge_policy_standard_approval_criteria_report", "")
    ).strip()
    approval_eligible_review_path = REPO_ROOT / str(
        required_inputs.get("bridge_approval_eligible_policy_review_outcome_report", "")
    ).strip()
    approval_record_surface_path = REPO_ROOT / str(
        required_inputs.get("bridge_policy_standard_approval_record_surface_report", "")
    ).strip()
    execution_report_relpath = str(
        required_inputs.get("bridge_policy_standard_approval_recordation_execution_report", "")
    ).strip()
    note_path = REPO_ROOT / str(required_inputs.get("policy_standard_approval_record_note", "")).strip()

    approval_criteria = _read_json(approval_criteria_path)
    approval_eligible_review = _read_json(approval_eligible_review_path)
    approval_record_surface = _read_json(approval_record_surface_path)
    execution_report = None
    execution_report_path = None
    if execution_report_relpath:
        candidate_execution_report_path = REPO_ROOT / execution_report_relpath
        if candidate_execution_report_path.exists():
            execution_report_path = candidate_execution_report_path
            execution_report = _read_json(candidate_execution_report_path)
    note_text = _read_text(note_path)

    approval_criteria_summary = dict(approval_criteria.get("summary", {}))
    approval_eligible_review_summary = dict(approval_eligible_review.get("summary", {}))
    approval_record_surface_summary = dict(approval_record_surface.get("summary", {}))
    execution_summary = dict(execution_report.get("summary", {})) if execution_report else {}

    approval_criteria_outcome = str(approval_criteria_summary.get("terminal_outcome", "")).strip()
    approval_eligible_review_outcome = str(
        approval_eligible_review_summary.get("terminal_outcome", "")
    ).strip()
    approval_record_surface_outcome = str(
        approval_record_surface_summary.get("terminal_outcome", "")
    ).strip()

    required_policy_standard_approval_criteria_outcome = str(
        policy.get("required_policy_standard_approval_criteria_outcome", "")
    ).strip()
    required_approval_eligible_policy_review_outcome = str(
        policy.get("required_approval_eligible_policy_review_outcome", "")
    ).strip()
    required_policy_standard_approval_record_surface_outcome = str(
        policy.get("required_policy_standard_approval_record_surface_outcome", "")
    ).strip()
    required_note_tokens = list(policy.get("required_note_tokens", []))
    required_approval_record_fields = list(policy.get("required_approval_record_fields", []))

    policy_standard_approval_record_defined = bool(policy.get("policy_standard_approval_record_defined", False))
    declared_approval_record_fields_present = bool(policy.get("approval_record_fields_present", False))
    declared_policy_standard_approval_recorded = bool(policy.get("policy_standard_approval_recorded", False))

    execution_terminal_outcome = _maybe_text(execution_summary.get("terminal_outcome"))
    execution_field_values = [_maybe_text(execution_summary.get(field)) for field in required_approval_record_fields]
    execution_approval_record_fields_present = bool(required_approval_record_fields) and all(
        execution_field_values
    )
    execution_policy_standard_approval_recorded = bool(
        execution_summary.get("policy_standard_approval_recorded", False)
    )
    execution_surface_usable = execution_terminal_outcome in {
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_READY_BUT_UNRECORDED",
        "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_RECORDED",
        "",
    }

    if execution_report is not None:
        approval_record_fields_present = execution_approval_record_fields_present
        policy_standard_approval_recorded = execution_policy_standard_approval_recorded
    else:
        approval_record_fields_present = declared_approval_record_fields_present
        policy_standard_approval_recorded = declared_policy_standard_approval_recorded

    note_tokens_present = all(token in note_text for token in required_note_tokens)
    policy_shape_ok = all(
        key in policy
        for key in [
            "required_policy_standard_approval_criteria_outcome",
            "required_approval_eligible_policy_review_outcome",
            "required_policy_standard_approval_record_surface_outcome",
            "required_note_tokens",
            "policy_standard_approval_record_defined",
            "required_approval_record_fields",
            "approval_record_fields_present",
            "policy_standard_approval_recorded",
            "single_layer_only",
            "single_outcome_only",
        ]
    )

    record_state_valid = (
        (not approval_record_fields_present and not policy_standard_approval_recorded)
        or (
            approval_record_fields_present
            and policy_standard_approval_recorded
            and execution_terminal_outcome
            == "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_RECORDED"
        )
    )

    preconditions_ok = (
        approval_criteria_outcome == required_policy_standard_approval_criteria_outcome
        and approval_eligible_review_outcome == required_approval_eligible_policy_review_outcome
        and approval_record_surface_outcome == required_policy_standard_approval_record_surface_outcome
        and note_tokens_present
        and policy_standard_approval_record_defined
        and bool(required_approval_record_fields)
        and execution_surface_usable
        and record_state_valid
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    default_outcome = str(
        contract.get(
            "default_outcome",
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_EVIDENCE_INCOMPLETE",
        )
    ).strip()

    if not policy_shape_ok:
        terminal_outcome = "HOLD_PENDING_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_REPAIR"
        next_action = "REPAIR_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SHAPE"
    elif preconditions_ok:
        terminal_outcome = "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_DECLARED"
        next_action = "RETAIN_FAIL_CLOSED_POLICY_UNTIL_A_VALID_APPROVAL_RECORD_WITH_REQUIRED_FIELDS_IS_WRITTEN"
    else:
        terminal_outcome = "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_PRECONDITIONS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "policy_standard_approval_criteria_outcome_match": approval_criteria_outcome
            == required_policy_standard_approval_criteria_outcome,
            "approval_eligible_policy_review_outcome_match": approval_eligible_review_outcome
            == required_approval_eligible_policy_review_outcome,
            "policy_standard_approval_record_surface_outcome_match": approval_record_surface_outcome
            == required_policy_standard_approval_record_surface_outcome,
            "note_tokens_present": note_tokens_present,
            "policy_standard_approval_record_defined": policy_standard_approval_record_defined,
            "approval_record_fields_present": approval_record_fields_present,
            "policy_standard_approval_recorded": policy_standard_approval_recorded,
            "single_terminal_outcome_rule_declared": str(
                contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_OUTCOME",
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "approval_record_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "policy_standard_approval_criteria_outcome": approval_criteria_outcome,
                "approval_eligible_policy_review_outcome": approval_eligible_review_outcome,
                "policy_standard_approval_record_surface_outcome": approval_record_surface_outcome,
                "approval_recordation_execution_outcome": execution_terminal_outcome or None,
                "policy_standard_approval_record_defined": policy_standard_approval_record_defined,
                "required_approval_record_fields": required_approval_record_fields,
                "approval_record_fields_present": approval_record_fields_present,
                "policy_standard_approval_recorded": policy_standard_approval_recorded,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "policy_standard_approval_record_defined": policy_standard_approval_record_defined,
            "required_approval_record_fields": required_approval_record_fields,
            "approval_record_fields_present": approval_record_fields_present,
            "policy_standard_approval_recorded": policy_standard_approval_recorded,
            "next_action": next_action,
            "single_layer_only": bool(policy.get("single_layer_only", True)),
            "single_outcome_only": bool(policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_policy_standard_approval_criteria_report": _ptr(approval_criteria_path),
            "bridge_approval_eligible_policy_review_outcome_report": _ptr(approval_eligible_review_path),
            "bridge_policy_standard_approval_record_surface_report": _ptr(approval_record_surface_path),
            "bridge_policy_standard_approval_recordation_execution_report": (
                _ptr(execution_report_path) if execution_report_path is not None else None
            ),
            "policy_standard_approval_record_note": _ptr(note_path),
        },
        "non_claim_boundary": "Repository-local RL10 bridge policy standard approval-record report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the RL10 bridge policy standard approval-record report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_record_20260414_v0.json",
    )
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
        "qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_record_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())