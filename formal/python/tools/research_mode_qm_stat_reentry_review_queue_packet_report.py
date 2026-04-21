from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_REPORT_20260420_v0"
DEFAULT_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_20260420_v0.md"
)
DEFAULT_PACKET_OBJECT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "queue"
    / "qm_stat_reentry_review_queue_packet_20260420_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "research_mode_qm_stat_reentry_review_queue_packet_20260420_v0.json"
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


def build_payload(*, packet_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    packet_text = _read_text(packet_path)

    queue_report_path = REPO_ROOT / "formal/output/reports/research_mode_qm_stat_reentry_review_cycle_queue_20260419_v0.json"
    queue_object_path = REPO_ROOT / "formal/output/queue/qm_stat_reentry_review_cycle_queue_20260419_v0.json"
    eligibility_path = REPO_ROOT / "formal/output/reports/research_mode_qm_stat_reentry_eligibility_review_20260419_v0.json"
    support_path = REPO_ROOT / "formal/output/reports/research_mode_qm_stat_reentry_support_artifact_20260419_v0.json"

    queue_report = _read_json(queue_report_path)
    queue_object = _read_json(queue_object_path)
    eligibility_report = _read_json(eligibility_path)
    support_report = _read_json(support_path)

    queue_summary = dict(queue_report.get("summary", {}))
    queue_criteria = dict(queue_report.get("criteria", {}))
    queue_binding = dict(queue_object.get("target_binding", {}))
    eligibility_summary = dict(eligibility_report.get("summary", {}))
    support_summary = dict(support_report.get("summary", {}))

    packet_tokens_ok = all(
        token in packet_text
        for token in (
            "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_ID_v0:",
            "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_STATUS_v0: AUTHORED_BOUNDED_v0_NONCLAIM",
            "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_OUTCOME_SET_v0:",
            "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_NONCANONICAL_RULE_v0:",
            "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_NEXT_ACTION_v0: HAND_OFF_ONE_BOUNDED_QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_FOR_DOWNSTREAM_INTAKE_DECISION",
        )
    )
    queue_ready_for_packet_authoring = all(
        [
            queue_summary.get("terminal_outcome") == "QM_STAT_REENTRY_REVIEW_CYCLE_QUEUED_FOR_ONE_BOUNDED_REVIEW",
            queue_summary.get("queue_status") == "QUEUED_FOR_ONE_BOUNDED_REENTRY_REVIEW_CYCLE",
            queue_summary.get("queue_packet_status") == "PENDING_REENTRY_QUEUE_PACKET_AUTHORING",
            queue_summary.get("next_action") == "AUTHOR_ONE_BOUNDED_QM_STAT_REENTRY_REVIEW_QUEUE_PACKET",
            queue_criteria.get("eligibility_ready_for_queue") is True,
            queue_criteria.get("support_artifact_ready_for_queue") is True,
            queue_criteria.get("target_binding_preserved") is True,
        ]
    )
    binding_preserved = all(
        [
            queue_binding.get("row_id") == "ROW-SEAM-QM-STAT-001",
            queue_binding.get("seam_id") == "SEAM-QM-STAT",
            queue_binding.get("target_package_id") == "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
            eligibility_summary.get("target_row_id") == queue_binding.get("row_id"),
            eligibility_summary.get("target_seam_id") == queue_binding.get("seam_id"),
            eligibility_summary.get("target_package_id") == queue_binding.get("target_package_id"),
            support_summary.get("target_row_id") == queue_binding.get("row_id"),
            support_summary.get("target_seam_id") == queue_binding.get("seam_id"),
            support_summary.get("target_package_id") == queue_binding.get("target_package_id"),
        ]
    )
    support_authorization_ready = all(
        [
            support_summary.get("terminal_outcome") == "QM_STAT_REENTRY_SUPPORT_ARTIFACT_MATERIALIZED_AND_QUEUE_AUTHORIZED",
            support_summary.get("authorization_status") == "AUTHORIZED_FOR_ONE_BOUNDED_REENTRY_QUEUE_DECISION",
            support_summary.get("authorized_candidate_target")
            == "ROW-SEAM-QM-STAT-001::QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
        ]
    )

    if not packet_tokens_ok:
        terminal_outcome = "QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_BLOCKED_BY_MISSING_PACKET_FIELDS"
        next_action = "REPAIR_QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_FIELDS"
    elif queue_ready_for_packet_authoring and binding_preserved and support_authorization_ready:
        terminal_outcome = "QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_AUTHORED_FOR_BOUNDED_HANDOFF"
        next_action = "HAND_OFF_ONE_BOUNDED_QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_FOR_DOWNSTREAM_INTAKE_DECISION"
    elif queue_ready_for_packet_authoring and support_authorization_ready:
        terminal_outcome = "QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_HELD_PENDING_TARGET_BINDING_REPAIR"
        next_action = "RESTORE_QM_STAT_REENTRY_PACKET_TARGET_BINDING_BEFORE_HANDOFF"
    else:
        terminal_outcome = "QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_QM_STAT_REENTRY_QUEUE_PACKET_PREREQUISITES_AND_RERUN"

    packet_object = {
        "queue_packet_id": "qm_stat_reentry_review_queue_packet_20260420_v0",
        "queue_packet_class": "BOUNDED_REENTRY_REVIEW_QUEUE_PACKET",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "queue_packet_status": "AUTHORED_BOUNDED_v0_NONCLAIM"
        if terminal_outcome == "QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_AUTHORED_FOR_BOUNDED_HANDOFF"
        else "INCOMPLETE_PACKET",
        "handoff_status": "READY_FOR_DOWNSTREAM_INTAKE_DECISION"
        if terminal_outcome == "QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_AUTHORED_FOR_BOUNDED_HANDOFF"
        else "NOT_READY_FOR_HANDOFF",
        "authorized_candidate_target": "ROW-SEAM-QM-STAT-001::QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
        "queue_scope_token": "ONE_BOUNDED_QM_STAT_REENTRY_REVIEW_CYCLE_ONLY",
        "target_binding": {
            "row_id": "ROW-SEAM-QM-STAT-001",
            "seam_id": "SEAM-QM-STAT",
            "target_package_id": "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
        },
        "source_bundle": {
            "queue_report": _ptr(queue_report_path),
            "queue_object": _ptr(queue_object_path),
            "eligibility_report": _ptr(eligibility_path),
            "support_artifact_report": _ptr(support_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT re-entry review queue packet only; no canonical promotion, canonical mutation, or seam-closure claim.",
    }

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": packet_object["captured_at_utc"],
        "criteria": {
            "packet_required_tokens_present": packet_tokens_ok,
            "queue_ready_for_packet_authoring": queue_ready_for_packet_authoring,
            "target_binding_preserved": binding_preserved,
            "support_authorization_preserved": support_authorization_ready,
            "single_outcome_materialized": True,
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome
                in {
                    "QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_AUTHORED_FOR_BOUNDED_HANDOFF",
                    "QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_BLOCKED_BY_MISSING_PACKET_FIELDS",
                    "QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_HELD_PENDING_TARGET_BINDING_REPAIR",
                    "QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_EVIDENCE_INCOMPLETE",
                },
                "single_outcome_materialized": True,
                "noncanonical_boundary_preserved": True,
                "handoff_requires_downstream_intake_decision": True,
            },
            "inputs": {
                "queue_terminal_outcome": queue_summary.get("terminal_outcome"),
                "queue_packet_status": queue_summary.get("queue_packet_status"),
                "eligibility_terminal_outcome": eligibility_summary.get("terminal_outcome"),
                "support_terminal_outcome": support_summary.get("terminal_outcome"),
                "authorized_candidate_target": packet_object["authorized_candidate_target"],
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome
                == "QM_STAT_REENTRY_REVIEW_QUEUE_PACKET_AUTHORED_FOR_BOUNDED_HANDOFF",
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "queue_packet_status": packet_object["queue_packet_status"],
            "handoff_status": packet_object["handoff_status"],
            "authorized_candidate_target": packet_object["authorized_candidate_target"],
            "target_row_id": packet_object["target_binding"]["row_id"],
            "target_seam_id": packet_object["target_binding"]["seam_id"],
            "target_package_id": packet_object["target_binding"]["target_package_id"],
            "canonical_mutation_emitted": False,
            "next_action": next_action,
        },
        "queue_packet_object": packet_object,
        "source_bundle": packet_object["source_bundle"],
        "non_claim_boundary": packet_object["non_claim_boundary"],
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT re-entry review queue-packet report.")
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument("--packet-out", type=Path, default=DEFAULT_PACKET_OBJECT_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    packet_out = ns.packet_out if ns.packet_out.is_absolute() else (REPO_ROOT / ns.packet_out)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_payload(packet_path=packet_path, captured_at_utc=ns.captured_at_utc)
    packet_out.parent.mkdir(parents=True, exist_ok=True)
    out.parent.mkdir(parents=True, exist_ok=True)
    packet_out.write_text(json.dumps(payload["queue_packet_object"], indent=2, sort_keys=True) + "\n", encoding="utf-8")
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "research_mode_qm_stat_reentry_review_queue_packet_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())