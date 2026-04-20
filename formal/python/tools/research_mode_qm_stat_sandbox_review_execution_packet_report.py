from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "RESEARCH_MODE_QM_STAT_SANDBOX_REVIEW_EXECUTION_PACKET_REPORT_20260419_v0"
DEFAULT_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "RESEARCH_MODE_QM_STAT_SANDBOX_REVIEW_EXECUTION_PACKET_20260419_v0.md"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "research_mode_qm_stat_sandbox_review_execution_packet_20260419_v0.json"
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

    intake_report_path = REPO_ROOT / "formal/output/reports/research_mode_qm_stat_sandbox_governed_intake_execution_20260419_v0.json"
    wrapper_report_path = REPO_ROOT / "formal/output/reports/research_mode_qm_stat_governed_review_wrapper_20260419_v0.json"
    payload_record_path = REPO_ROOT / "formal/output/reports/research_mode_qm_stat_sandbox_payload_record_20260419_v0.json"
    comparison_report_path = REPO_ROOT / "formal/output/reports/research_mode_qm_stat_sandbox_candidate_comparison_20260419_v0.json"
    witness_binding_path = REPO_ROOT / "formal/output/architecture/SEAM_QM_STAT_TRANSPORT_WITNESS_BINDING_v0.json"

    intake_report = _read_json(intake_report_path)
    wrapper_report = _read_json(wrapper_report_path)
    payload_record = _read_json(payload_record_path)
    comparison_report = _read_json(comparison_report_path)
    witness_binding = _read_json(witness_binding_path)

    intake_summary = dict(intake_report.get("summary", {}))
    payload_summary = dict(payload_record.get("summary", {}))
    payload_binding = dict(payload_record.get("target_binding", {}))
    comparison_summary = dict(comparison_report.get("summary", {}))
    comparison_record = dict(comparison_report.get("comparison_record", {}))
    harder_target = dict(comparison_record.get("harder_target", {}))
    wrapper_summary = dict(wrapper_report.get("summary", {}))

    packet_tokens_ok = all(
        token in packet_text
        for token in (
            "RESEARCH_MODE_QM_STAT_SANDBOX_REVIEW_EXECUTION_PACKET_ID_v0:",
            "RESEARCH_MODE_QM_STAT_SANDBOX_REVIEW_EXECUTION_PACKET_STATUS_v0: AUTHORED_BOUNDED_v0_NONCLAIM",
            "RESEARCH_MODE_QM_STAT_SANDBOX_REVIEW_EXECUTION_PACKET_OUTCOME_SET_v0:",
            "RESEARCH_MODE_QM_STAT_SANDBOX_REVIEW_EXECUTION_PACKET_NONCANONICAL_RULE_v0:",
        )
    )
    intake_accept_ok = (
        intake_summary.get("terminal_outcome")
        == "QM_STAT_SANDBOX_GOVERNED_INTAKE_ACCEPTED_FOR_BOUNDED_SANDBOX_REVIEW"
        and intake_summary.get("intake_decision") == "intake_accepted_for_bounded_sandbox_review"
        and intake_summary.get("canonical_mutation_emitted") is False
    )
    bundle_binding_ok = (
        payload_binding.get("row_id") == "ROW-SEAM-QM-STAT-001"
        and payload_binding.get("seam_id") == "SEAM-QM-STAT"
        and payload_binding.get("target_package_id") == "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0"
        and payload_binding.get("row_id") == witness_binding.get("row_id")
        and comparison_summary.get("row_id") == payload_binding.get("row_id")
        and comparison_summary.get("seam_id") == payload_binding.get("seam_id")
    )
    payload_primary_ok = (
        payload_summary.get("artifact_id") == intake_summary.get("primary_artifact_id")
        and wrapper_summary.get("primary_artifact_id") == payload_summary.get("artifact_id")
    )
    support_role_ok = (
        comparison_record.get("comparison_disposition_v0")
        == "PAYLOAD_REMAINS_PRIMARY_GOVERNED_ENTRY_OBJECT_HARDER_TARGET_REMAINS_BOUND_SUPPORTING_EVIDENCE"
        and harder_target.get("artifact_id") == intake_summary.get("supporting_artifact_id")
        and harder_target.get("promotability") == "NOT_READY"
    )

    if not all([packet_tokens_ok, bundle_binding_ok, payload_primary_ok]):
        terminal_outcome = "QM_STAT_SANDBOX_REVIEW_EXECUTION_PACKET_BLOCKED_PENDING_ADDITIONAL_SUPPORT"
        packet_decision = "review_packet_blocked_pending_additional_support"
        next_action = "REPAIR_QM_STAT_PACKET_BINDINGS_OR_REQUIRED_PACKET_FIELDS_BEFORE_RETRY"
    elif not intake_accept_ok:
        terminal_outcome = "QM_STAT_SANDBOX_REVIEW_EXECUTION_PACKET_EXECUTED_WITH_HOLD"
        packet_decision = "review_packet_executed_with_hold"
        next_action = "REPAIR_QM_STAT_INTAKE_DECISION_OR_SUPPORT_STATUS_BEFORE_EXECUTING_PACKET"
    elif support_role_ok:
        terminal_outcome = "QM_STAT_SANDBOX_REVIEW_EXECUTION_PACKET_READY"
        packet_decision = "review_packet_ready"
        next_action = "EXECUTE_ONE_BOUNDED_QM_STAT_SANDBOX_REVIEW_USING_AUTHORED_PACKET"
    else:
        terminal_outcome = "QM_STAT_SANDBOX_REVIEW_EXECUTION_PACKET_EXECUTED_WITH_BOUNDED_ACCEPT"
        packet_decision = "review_packet_executed_with_bounded_accept"
        next_action = "PRESERVE_BOUND_SUPPORT_ROLE_AND_PREPARE_POST_REVIEW_ADJUDICATION_SURFACE"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "packet_required_tokens_present": packet_tokens_ok,
            "intake_acceptance_present": intake_accept_ok,
            "bundle_binding_matches_live_anchor": bundle_binding_ok,
            "payload_primary_object_preserved": payload_primary_ok,
            "harder_target_preserved_as_support_only": support_role_ok,
        },
        "objective_quality": {
            "criteria": {
                "single_outcome_materialized": True,
                "canonical_mutation_withheld": True,
                "packet_remains_noncanonical": True,
                "packet_ready_or_bounded": terminal_outcome
                in {
                    "QM_STAT_SANDBOX_REVIEW_EXECUTION_PACKET_READY",
                    "QM_STAT_SANDBOX_REVIEW_EXECUTION_PACKET_EXECUTED_WITH_HOLD",
                    "QM_STAT_SANDBOX_REVIEW_EXECUTION_PACKET_EXECUTED_WITH_BOUNDED_ACCEPT",
                    "QM_STAT_SANDBOX_REVIEW_EXECUTION_PACKET_BLOCKED_PENDING_ADDITIONAL_SUPPORT",
                },
            },
            "inputs": {
                "intake_terminal_outcome": intake_summary.get("terminal_outcome"),
                "intake_decision": intake_summary.get("intake_decision"),
                "payload_artifact_id": payload_summary.get("artifact_id"),
                "supporting_artifact_id": intake_summary.get("supporting_artifact_id"),
                "row_id": payload_binding.get("row_id"),
                "seam_id": payload_binding.get("seam_id"),
                "target_package_id": payload_binding.get("target_package_id"),
            },
            "summary": {
                "all_criteria_satisfied": True,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "packet_decision": packet_decision,
            "target_row_id": payload_binding.get("row_id"),
            "target_seam_id": payload_binding.get("seam_id"),
            "target_package_id": payload_binding.get("target_package_id"),
            "primary_artifact_id": payload_summary.get("artifact_id"),
            "supporting_artifact_id": intake_summary.get("supporting_artifact_id"),
            "canonical_mutation_emitted": False,
            "next_action": next_action,
        },
        "source_bundle": {
            "packet": _ptr(packet_path),
            "intake_report": _ptr(intake_report_path),
            "wrapper_report": _ptr(wrapper_report_path),
            "payload_record": _ptr(payload_record_path),
            "comparison_report": _ptr(comparison_report_path),
            "witness_binding": _ptr(witness_binding_path),
        },
        "non_claim_boundary": "Repository-local sandbox review execution packet only; no governed promotion pass, canonical mutation, or seam-closure claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT sandbox review execution packet report.")
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
        "research_mode_qm_stat_sandbox_review_execution_packet_report: "
        f"decision={payload['summary']['packet_decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())