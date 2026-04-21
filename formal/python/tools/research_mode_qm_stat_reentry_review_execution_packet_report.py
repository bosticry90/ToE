from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_EXECUTION_PACKET_REPORT_20260420_v0"
DEFAULT_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_EXECUTION_PACKET_20260420_v0.md"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "research_mode_qm_stat_reentry_review_execution_packet_20260420_v0.json"
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


def build_report(*, packet_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    packet_text = _read_text(packet_path)

    intake_report_path = REPO_ROOT / "formal/output/reports/research_mode_qm_stat_reentry_downstream_intake_decision_20260420_v0.json"
    queue_packet_report_path = REPO_ROOT / "formal/output/reports/research_mode_qm_stat_reentry_review_queue_packet_20260420_v0.json"
    queue_packet_object_path = REPO_ROOT / "formal/output/queue/qm_stat_reentry_review_queue_packet_20260420_v0.json"
    queue_report_path = REPO_ROOT / "formal/output/reports/research_mode_qm_stat_reentry_review_cycle_queue_20260419_v0.json"

    intake_report = _read_json(intake_report_path)
    queue_packet_report = _read_json(queue_packet_report_path)
    queue_packet_object = _read_json(queue_packet_object_path)
    queue_report = _read_json(queue_report_path)

    intake_summary = dict(intake_report.get("summary", {}))
    intake_criteria = dict(intake_report.get("criteria", {}))
    queue_packet_summary = dict(queue_packet_report.get("summary", {}))
    queue_packet_criteria = dict(queue_packet_report.get("criteria", {}))
    queue_packet_object_report = dict(queue_packet_report.get("queue_packet_object", {}))
    queue_packet_binding = dict(queue_packet_object.get("target_binding", {}))
    queue_summary = dict(queue_report.get("summary", {}))
    queue_binding = dict(queue_report.get("queue_object", {})).get("target_binding", {})

    packet_tokens_ok = all(
        token in packet_text
        for token in (
            "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_EXECUTION_PACKET_ID_v0:",
            "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_EXECUTION_PACKET_STATUS_v0: AUTHORED_BOUNDED_v0_NONCLAIM",
            "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_EXECUTION_PACKET_OUTCOME_SET_v0:",
            "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_EXECUTION_PACKET_NONCANONICAL_RULE_v0:",
            "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_EXECUTION_PACKET_NEXT_ACTION_v0: EXECUTE_ONE_BOUNDED_QM_STAT_REENTRY_REVIEW_USING_AUTHORED_PACKET_WITHOUT_CANONICAL_MUTATION",
        )
    )
    intake_accept_ok = all(
        [
            intake_summary.get("terminal_outcome")
            == "QM_STAT_REENTRY_DOWNSTREAM_INTAKE_ACCEPTED_FOR_BOUNDED_EXECUTION_PACKET_AUTHORING",
            intake_summary.get("intake_decision") == "reentry_intake_accepted_for_bounded_execution_packet_authoring",
            intake_summary.get("next_action")
            == "AUTHOR_ONE_BOUNDED_QM_STAT_REENTRY_REVIEW_EXECUTION_PACKET_WITHOUT_CANONICAL_MUTATION",
            intake_summary.get("canonical_mutation_emitted") is False,
            intake_criteria.get("packet_ready_for_intake") is True,
            intake_criteria.get("target_binding_preserved") is True,
        ]
    )
    binding_ok = all(
        [
            queue_packet_binding.get("row_id") == "ROW-SEAM-QM-STAT-001",
            queue_packet_binding.get("seam_id") == "SEAM-QM-STAT",
            queue_packet_binding.get("target_package_id") == "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
            queue_packet_summary.get("authorized_candidate_target")
            == "ROW-SEAM-QM-STAT-001::QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
            queue_packet_object_report.get("target_binding", {}).get("row_id") == queue_packet_binding.get("row_id"),
            queue_binding.get("row_id") == queue_packet_binding.get("row_id"),
            queue_binding.get("seam_id") == queue_packet_binding.get("seam_id"),
            queue_binding.get("target_package_id") == queue_packet_binding.get("target_package_id"),
            intake_summary.get("target_row_id") == queue_packet_binding.get("row_id"),
            intake_summary.get("target_seam_id") == queue_packet_binding.get("seam_id"),
            intake_summary.get("target_package_id") == queue_packet_binding.get("target_package_id"),
        ]
    )
    queue_anchor_ok = all(
        [
            queue_summary.get("terminal_outcome") == "QM_STAT_REENTRY_REVIEW_CYCLE_QUEUED_FOR_ONE_BOUNDED_REVIEW",
            queue_summary.get("queue_status") == "QUEUED_FOR_ONE_BOUNDED_REENTRY_REVIEW_CYCLE",
            queue_summary.get("canonical_mutation_emitted") is False,
            queue_packet_summary.get("terminal_outcome") == "QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_AUTHORED_FOR_BOUNDED_HANDOFF",
            queue_packet_summary.get("handoff_status") == "READY_FOR_DOWNSTREAM_INTAKE_DECISION",
            queue_packet_summary.get("queue_packet_status") == "AUTHORED_BOUNDED_v0_NONCLAIM",
            queue_packet_criteria.get("queue_ready_for_packet_authoring") is True,
        ]
    )

    if not all([packet_tokens_ok, binding_ok, queue_anchor_ok]):
        terminal_outcome = "QM_STAT_REENTRY_REVIEW_EXECUTION_PACKET_BLOCKED_BY_BINDING_OR_CONTRACT_GAP"
        packet_decision = "reentry_review_execution_packet_blocked"
        next_action = "REPAIR_QM_STAT_REENTRY_REVIEW_EXECUTION_PACKET_CONTRACT_OR_BINDINGS"
    elif not intake_accept_ok:
        terminal_outcome = "QM_STAT_REENTRY_REVIEW_EXECUTION_PACKET_HELD_PENDING_INTAKE_ACCEPTANCE"
        packet_decision = "reentry_review_execution_packet_held"
        next_action = "RESTORE_ACCEPTED_REENTRY_DOWNSTREAM_INTAKE_DECISION_BEFORE_PACKET_USE"
    else:
        terminal_outcome = "QM_STAT_REENTRY_REVIEW_EXECUTION_PACKET_READY"
        packet_decision = "reentry_review_execution_packet_ready"
        next_action = "EXECUTE_ONE_BOUNDED_QM_STAT_REENTRY_REVIEW_USING_AUTHORED_PACKET_WITHOUT_CANONICAL_MUTATION"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "packet_required_tokens_present": packet_tokens_ok,
            "intake_acceptance_present": intake_accept_ok,
            "target_binding_preserved": binding_ok,
            "queue_anchor_preserved": queue_anchor_ok,
            "single_outcome_materialized": True,
        },
        "objective_quality": {
            "criteria": {
                "packet_ready_or_bounded": terminal_outcome
                in {
                    "QM_STAT_REENTRY_REVIEW_EXECUTION_PACKET_READY",
                    "QM_STAT_REENTRY_REVIEW_EXECUTION_PACKET_HELD_PENDING_INTAKE_ACCEPTANCE",
                    "QM_STAT_REENTRY_REVIEW_EXECUTION_PACKET_BLOCKED_BY_BINDING_OR_CONTRACT_GAP",
                },
                "single_outcome_materialized": True,
                "canonical_mutation_withheld": True,
                "packet_remains_noncanonical": True,
                "review_execution_not_yet_started": True,
            },
            "inputs": {
                "intake_terminal_outcome": intake_summary.get("terminal_outcome"),
                "intake_decision": intake_summary.get("intake_decision"),
                "queue_packet_terminal_outcome": queue_packet_summary.get("terminal_outcome"),
                "authorized_candidate_target": intake_summary.get("authorized_candidate_target"),
                "row_id": queue_packet_binding.get("row_id"),
                "seam_id": queue_packet_binding.get("seam_id"),
                "target_package_id": queue_packet_binding.get("target_package_id"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome == "QM_STAT_REENTRY_REVIEW_EXECUTION_PACKET_READY",
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "packet_decision": packet_decision,
            "authorized_candidate_target": intake_summary.get("authorized_candidate_target"),
            "target_row_id": queue_packet_binding.get("row_id"),
            "target_seam_id": queue_packet_binding.get("seam_id"),
            "target_package_id": queue_packet_binding.get("target_package_id"),
            "canonical_mutation_emitted": False,
            "next_action": next_action,
        },
        "source_bundle": {
            "packet": _ptr(packet_path),
            "intake_report": _ptr(intake_report_path),
            "queue_packet_report": _ptr(queue_packet_report_path),
            "queue_packet_object": _ptr(queue_packet_object_path),
            "queue_report": _ptr(queue_report_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT re-entry review execution packet only; no re-entry review execution, canonical mutation, or seam-closure claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT re-entry review execution packet report.")
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(packet_path=packet_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "research_mode_qm_stat_reentry_review_execution_packet_report: "
        f"decision={payload['summary']['packet_decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())