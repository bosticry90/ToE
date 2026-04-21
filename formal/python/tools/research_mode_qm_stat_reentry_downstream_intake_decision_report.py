from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "RESEARCH_MODE_QM_STAT_REENTRY_DOWNSTREAM_INTAKE_DECISION_REPORT_20260420_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "RESEARCH_MODE_QM_STAT_REENTRY_DOWNSTREAM_INTAKE_DECISION_20260420_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "research_mode_qm_stat_reentry_downstream_intake_decision_20260420_v0.json"
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
    intake_policy = dict(declaration.get("intake_policy", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))

    queue_packet_note_path = REPO_ROOT / str(required_inputs.get("queue_packet_note", "")).strip()
    queue_packet_report_path = REPO_ROOT / str(required_inputs.get("queue_packet_report", "")).strip()
    queue_packet_object_path = REPO_ROOT / str(required_inputs.get("queue_packet_object", "")).strip()
    queue_report_path = REPO_ROOT / str(required_inputs.get("queue_report", "")).strip()

    queue_packet_note_text = _read_text(queue_packet_note_path)
    queue_packet_report = _read_json(queue_packet_report_path)
    queue_packet_object = _read_json(queue_packet_object_path)
    queue_report = _read_json(queue_report_path)

    packet_summary = dict(queue_packet_report.get("summary", {}))
    packet_criteria = dict(queue_packet_report.get("criteria", {}))
    packet_report_object = dict(queue_packet_report.get("queue_packet_object", {}))
    packet_binding = dict(queue_packet_object.get("target_binding", {}))
    queue_summary = dict(queue_report.get("summary", {}))
    queue_object = dict(queue_report.get("queue_object", {}))
    queue_binding = dict(queue_object.get("target_binding", {}))

    packet_contract_ok = all(
        token in queue_packet_note_text
        for token in (
            "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_STATUS_v0: AUTHORED_BOUNDED_v0_NONCLAIM",
            "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_SCOPE_v0: ONE_BOUNDED_QM_STAT_REENTRY_REVIEW_CYCLE_ONLY",
            "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_HANDOFF_RULE_v0: DOWNSTREAM_INTAKE_DECISION_REQUIRED_BEFORE_ANY_REENTRY_REVIEW_EXECUTION",
            "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_NEXT_ACTION_v0: HAND_OFF_ONE_BOUNDED_QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_FOR_DOWNSTREAM_INTAKE_DECISION",
        )
    )
    binding_ok = all(
        [
            packet_binding.get("row_id") == str(intake_policy.get("required_target_row", "")).strip(),
            packet_binding.get("seam_id") == str(intake_policy.get("required_target_seam", "")).strip(),
            packet_binding.get("target_package_id") == str(intake_policy.get("required_target_package_id", "")).strip(),
            packet_report_object.get("authorized_candidate_target")
            == str(intake_policy.get("required_authorized_candidate_target", "")).strip(),
            packet_report_object.get("target_binding", {}).get("row_id") == packet_binding.get("row_id"),
            packet_report_object.get("target_binding", {}).get("seam_id") == packet_binding.get("seam_id"),
            packet_report_object.get("target_binding", {}).get("target_package_id") == packet_binding.get("target_package_id"),
            queue_binding.get("row_id") == packet_binding.get("row_id"),
            queue_binding.get("seam_id") == packet_binding.get("seam_id"),
            queue_binding.get("target_package_id") == packet_binding.get("target_package_id"),
            queue_summary.get("authorized_candidate_target")
            == str(intake_policy.get("required_authorized_candidate_target", "")).strip(),
        ]
    )
    scope_ok = all(
        [
            queue_packet_object.get("queue_scope_token") == str(intake_policy.get("required_scope_token", "")).strip(),
            packet_report_object.get("queue_scope_token") == str(intake_policy.get("required_scope_token", "")).strip(),
            queue_object.get("queue_scope_token") == str(intake_policy.get("required_scope_token", "")).strip(),
        ]
    )
    queue_anchor_ok = all(
        [
            queue_summary.get("terminal_outcome") == str(intake_policy.get("required_queue_terminal_outcome", "")).strip(),
            queue_summary.get("queue_status") == str(intake_policy.get("required_queue_status", "")).strip(),
            queue_summary.get("canonical_mutation_emitted") is False,
        ]
    )
    packet_ready_for_intake = all(
        [
            packet_summary.get("terminal_outcome") == str(intake_policy.get("required_packet_terminal_outcome", "")).strip(),
            packet_summary.get("handoff_status") == str(intake_policy.get("required_handoff_status", "")).strip(),
            packet_summary.get("queue_packet_status") == str(intake_policy.get("required_packet_status", "")).strip(),
            packet_summary.get("next_action") == str(intake_policy.get("required_handoff_next_action", "")).strip(),
            packet_summary.get("authorized_candidate_target")
            == str(intake_policy.get("required_authorized_candidate_target", "")).strip(),
            packet_summary.get("canonical_mutation_emitted") is False,
            packet_criteria.get("packet_required_tokens_present") is True,
            packet_criteria.get("queue_ready_for_packet_authoring") is True,
            packet_criteria.get("target_binding_preserved") is True,
            packet_criteria.get("support_authorization_preserved") is True,
        ]
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "QM_STAT_REENTRY_DOWNSTREAM_INTAKE_HELD_PENDING_ADDED_SUPPORT")
    ).strip()

    if not all([packet_contract_ok, binding_ok, scope_ok, queue_anchor_ok]):
        terminal_outcome = "QM_STAT_REENTRY_DOWNSTREAM_INTAKE_REJECTED_DUE_TO_MISMATCH_OR_RULE_BREAK"
        intake_decision = "reentry_intake_rejected_due_to_mismatch_or_rule_break"
        next_action = str(intake_policy.get("next_action_on_reject", "")).strip()
    elif not packet_ready_for_intake:
        terminal_outcome = "QM_STAT_REENTRY_DOWNSTREAM_INTAKE_HELD_PENDING_ADDED_SUPPORT"
        intake_decision = "reentry_intake_held_pending_added_support"
        next_action = str(intake_policy.get("next_action_on_hold", "")).strip()
    else:
        terminal_outcome = "QM_STAT_REENTRY_DOWNSTREAM_INTAKE_ACCEPTED_FOR_BOUNDED_EXECUTION_PACKET_AUTHORING"
        intake_decision = "reentry_intake_accepted_for_bounded_execution_packet_authoring"
        next_action = str(intake_policy.get("next_action_on_accept", "")).strip()

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "packet_contract_present": packet_contract_ok,
            "target_binding_preserved": binding_ok,
            "single_scope_token_preserved": scope_ok,
            "queue_anchor_preserved": queue_anchor_ok,
            "packet_ready_for_intake": packet_ready_for_intake,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_QM_STAT_REENTRY_DOWNSTREAM_INTAKE_DECISION_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_QM_STAT_REENTRY_DOWNSTREAM_INTAKE_DECISION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "noncanonical_boundary_preserved": packet_summary.get("canonical_mutation_emitted") is False,
                "handoff_boundary_consumed_without_execution": True,
                "reentry_execution_not_yet_started": True,
            },
            "inputs": {
                "queue_packet_terminal_outcome": packet_summary.get("terminal_outcome"),
                "queue_packet_handoff_status": packet_summary.get("handoff_status"),
                "queue_packet_status": packet_summary.get("queue_packet_status"),
                "queue_terminal_outcome": queue_summary.get("terminal_outcome"),
                "queue_status": queue_summary.get("queue_status"),
                "authorized_candidate_target": packet_summary.get("authorized_candidate_target"),
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
            "target_row_id": packet_binding.get("row_id"),
            "target_seam_id": packet_binding.get("seam_id"),
            "target_package_id": packet_binding.get("target_package_id"),
            "authorized_candidate_target": packet_summary.get("authorized_candidate_target"),
            "canonical_mutation_emitted": False,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "queue_packet_note": _ptr(queue_packet_note_path),
            "queue_packet_report": _ptr(queue_packet_report_path),
            "queue_packet_object": _ptr(queue_packet_object_path),
            "queue_report": _ptr(queue_report_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT re-entry downstream intake decision only; no re-entry review execution, canonical mutation, or seam-closure claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT re-entry downstream intake decision report.")
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
        "research_mode_qm_stat_reentry_downstream_intake_decision_report: "
        f"decision={payload['summary']['intake_decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())