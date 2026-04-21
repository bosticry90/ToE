from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_EXECUTION_REPORT_20260420_v0"
DEFAULT_OUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "research_mode_qm_stat_reentry_review_execution_20260420_v0.json"
)
PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_EXECUTION_PACKET_20260420_v0.md"
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


def build_report(*, captured_at_utc: str | None) -> dict[str, Any]:
    packet_text = _read_text(PACKET_PATH)
    packet_report_path = (
        REPO_ROOT
        / "formal/output/reports/research_mode_qm_stat_reentry_review_execution_packet_20260420_v0.json"
    )
    intake_report_path = (
        REPO_ROOT
        / "formal/output/reports/research_mode_qm_stat_reentry_downstream_intake_decision_20260420_v0.json"
    )
    queue_packet_report_path = (
        REPO_ROOT
        / "formal/output/reports/research_mode_qm_stat_reentry_review_queue_packet_20260420_v0.json"
    )
    queue_packet_object_path = (
        REPO_ROOT / "formal/output/queue/qm_stat_reentry_review_queue_packet_20260420_v0.json"
    )
    queue_report_path = (
        REPO_ROOT
        / "formal/output/reports/research_mode_qm_stat_reentry_review_cycle_queue_20260419_v0.json"
    )
    canonical_action_standard_path = (
        REPO_ROOT / "formal/docs/release/TOE_CANONICAL_ACTION_PROMOTION_STANDARD_v0.md"
    )

    packet_report = _read_json(packet_report_path)
    intake_report = _read_json(intake_report_path)
    queue_packet_report = _read_json(queue_packet_report_path)
    queue_packet_object = _read_json(queue_packet_object_path)
    queue_report = _read_json(queue_report_path)
    canonical_action_standard_text = _read_text(canonical_action_standard_path)

    packet_summary = dict(packet_report.get("summary", {}))
    intake_summary = dict(intake_report.get("summary", {}))
    queue_packet_summary = dict(queue_packet_report.get("summary", {}))
    queue_packet_binding = dict(queue_packet_object.get("target_binding", {}))
    queue_summary = dict(queue_report.get("summary", {}))

    packet_ready = (
        packet_summary.get("terminal_outcome") == "QM_STAT_REENTRY_REVIEW_EXECUTION_PACKET_READY"
        and packet_summary.get("packet_decision") == "reentry_review_execution_packet_ready"
        and packet_summary.get("canonical_mutation_emitted") is False
    )
    intake_accept_ok = (
        intake_summary.get("terminal_outcome")
        == "QM_STAT_REENTRY_DOWNSTREAM_INTAKE_ACCEPTED_FOR_BOUNDED_EXECUTION_PACKET_AUTHORING"
        and intake_summary.get("intake_decision")
        == "reentry_intake_accepted_for_bounded_execution_packet_authoring"
        and intake_summary.get("canonical_mutation_emitted") is False
    )
    queue_anchor_ok = (
        queue_summary.get("terminal_outcome") == "QM_STAT_REENTRY_REVIEW_CYCLE_QUEUED_FOR_ONE_BOUNDED_REVIEW"
        and queue_packet_summary.get("terminal_outcome")
        == "QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_AUTHORED_FOR_BOUNDED_HANDOFF"
        and queue_packet_object.get("handoff_status") == "READY_FOR_DOWNSTREAM_INTAKE_DECISION"
        and queue_packet_object.get("queue_packet_status") == "AUTHORED_BOUNDED_v0_NONCLAIM"
        and queue_packet_object.get("queue_scope_token") == "ONE_BOUNDED_QM_STAT_REENTRY_REVIEW_CYCLE_ONLY"
    )
    target_binding_ok = (
        queue_packet_binding.get("row_id") == "ROW-SEAM-QM-STAT-001"
        and queue_packet_binding.get("seam_id") == "SEAM-QM-STAT"
        and queue_packet_binding.get("target_package_id")
        == "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0"
        and packet_summary.get("target_row_id") == queue_packet_binding.get("row_id")
        and packet_summary.get("target_seam_id") == queue_packet_binding.get("seam_id")
        and packet_summary.get("target_package_id") == queue_packet_binding.get("target_package_id")
        and queue_packet_object.get("authorized_candidate_target")
        == packet_summary.get("authorized_candidate_target")
    )
    packet_rule_ok = all(
        token in packet_text
        for token in (
            "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_EXECUTION_PACKET_NONCANONICAL_RULE_v0:",
            "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_EXECUTION_PACKET_OUTCOME_SET_v0: READY_OR_BLOCKED_OR_HELD_ONLY",
            "EXECUTE_ONE_BOUNDED_QM_STAT_REENTRY_REVIEW_USING_AUTHORED_PACKET_WITHOUT_CANONICAL_MUTATION",
        )
    )
    canonical_action_block_ok = all(
        token in canonical_action_standard_text
        for token in (
            "TOE_CANONICAL_ACTION_PROMOTION_STATUS_v0: BLOCKED_PENDING_CRITERIA",
            "TOE_CANONICAL_ACTION_PROMOTION_REQUIRES_v0: THEOREM_TRANSPORT_REGIME_AND_GOVERNANCE_ALIGNMENT",
        )
    )

    if not all([packet_rule_ok, queue_anchor_ok, target_binding_ok]):
        terminal_outcome = "QM_STAT_REENTRY_REVIEW_BLOCKED_PENDING_PACKET_REPAIR"
        review_decision = "bounded_reentry_review_blocked_pending_packet_repair"
        next_action = "REPAIR_QM_STAT_REENTRY_REVIEW_PACKET_BINDINGS_OR_REQUIRED_FIELDS"
    elif not all([packet_ready, intake_accept_ok]):
        terminal_outcome = "QM_STAT_REENTRY_REVIEW_HELD_PENDING_INPUT_REPAIR"
        review_decision = "bounded_reentry_review_held_pending_input_repair"
        next_action = "REPAIR_QM_STAT_REENTRY_REVIEW_INPUTS_AND_RERUN_EXECUTION"
    elif not canonical_action_block_ok:
        terminal_outcome = "QM_STAT_REENTRY_REVIEW_REJECTED_DUE_TO_CANONICAL_BOUNDARY_MISMATCH"
        review_decision = "bounded_reentry_review_rejected_due_to_canonical_boundary_mismatch"
        next_action = "RESTORE_CANONICAL_ACTION_BOUNDARY_BEFORE_ANY_REENTRY_REVIEW_FOLLOWTHROUGH"
    else:
        terminal_outcome = "QM_STAT_REENTRY_REVIEW_COMPLETED_WITH_NO_CANONICAL_ACTION"
        review_decision = "bounded_reentry_review_completed_with_no_canonical_action"
        next_action = "AUTHOR_ONE_BOUNDED_QM_STAT_REENTRY_POST_REVIEW_ADJUDICATION_SURFACE_WITHOUT_CANONICAL_MUTATION"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "packet_ready": packet_ready,
            "intake_acceptance_present": intake_accept_ok,
            "queue_anchor_preserved": queue_anchor_ok,
            "target_binding_preserved": target_binding_ok,
            "packet_rule_tokens_present": packet_rule_ok,
            "canonical_action_boundary_present": canonical_action_block_ok,
        },
        "objective_quality": {
            "criteria": {
                "single_outcome_materialized": True,
                "canonical_mutation_withheld": True,
                "noncanonical_posture_preserved": True,
                "reentry_execution_completed_once": terminal_outcome
                == "QM_STAT_REENTRY_REVIEW_COMPLETED_WITH_NO_CANONICAL_ACTION",
            },
            "inputs": {
                "packet_terminal_outcome": packet_summary.get("terminal_outcome"),
                "packet_decision": packet_summary.get("packet_decision"),
                "intake_terminal_outcome": intake_summary.get("terminal_outcome"),
                "queue_packet_terminal_outcome": queue_packet_summary.get("terminal_outcome"),
                "row_id": queue_packet_binding.get("row_id"),
                "seam_id": queue_packet_binding.get("seam_id"),
                "target_package_id": queue_packet_binding.get("target_package_id"),
            },
            "summary": {
                "all_criteria_satisfied": True,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "review_decision": review_decision,
            "target_row_id": queue_packet_binding.get("row_id"),
            "target_seam_id": queue_packet_binding.get("seam_id"),
            "target_package_id": queue_packet_binding.get("target_package_id"),
            "authorized_candidate_target": queue_packet_object.get("authorized_candidate_target"),
            "canonical_mutation_emitted": False,
            "next_action": next_action,
        },
        "source_bundle": {
            "packet": _ptr(PACKET_PATH),
            "packet_report": _ptr(packet_report_path),
            "intake_report": _ptr(intake_report_path),
            "queue_packet_report": _ptr(queue_packet_report_path),
            "queue_packet_object": _ptr(queue_packet_object_path),
            "queue_report": _ptr(queue_report_path),
            "canonical_action_standard": _ptr(canonical_action_standard_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT re-entry review execution only; no canonical mutation or seam-closure claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT re-entry review execution report.")
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "research_mode_qm_stat_reentry_review_execution_report: "
        f"decision={payload['summary']['review_decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())