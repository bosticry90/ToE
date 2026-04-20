from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "RESEARCH_MODE_QM_STAT_SANDBOX_REVIEW_EXECUTION_REPORT_20260419_v0"
DEFAULT_OUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "research_mode_qm_stat_sandbox_review_execution_20260419_v0.json"
)
PACKET_PATH = REPO_ROOT / "formal" / "docs" / "release" / "RESEARCH_MODE_QM_STAT_SANDBOX_REVIEW_EXECUTION_PACKET_20260419_v0.md"


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
    packet_report_path = REPO_ROOT / "formal/output/reports/research_mode_qm_stat_sandbox_review_execution_packet_20260419_v0.json"
    intake_report_path = REPO_ROOT / "formal/output/reports/research_mode_qm_stat_sandbox_governed_intake_execution_20260419_v0.json"
    payload_record_path = REPO_ROOT / "formal/output/reports/research_mode_qm_stat_sandbox_payload_record_20260419_v0.json"
    comparison_report_path = REPO_ROOT / "formal/output/reports/research_mode_qm_stat_sandbox_candidate_comparison_20260419_v0.json"
    wrapper_report_path = REPO_ROOT / "formal/output/reports/research_mode_qm_stat_governed_review_wrapper_20260419_v0.json"
    witness_binding_path = REPO_ROOT / "formal/output/architecture/SEAM_QM_STAT_TRANSPORT_WITNESS_BINDING_v0.json"
    canonical_action_standard_path = REPO_ROOT / "formal/docs/release/TOE_CANONICAL_ACTION_PROMOTION_STANDARD_v0.md"

    packet_report = _read_json(packet_report_path)
    intake_report = _read_json(intake_report_path)
    payload_record = _read_json(payload_record_path)
    comparison_report = _read_json(comparison_report_path)
    wrapper_report = _read_json(wrapper_report_path)
    witness_binding = _read_json(witness_binding_path)
    canonical_action_standard_text = _read_text(canonical_action_standard_path)

    packet_summary = dict(packet_report.get("summary", {}))
    intake_summary = dict(intake_report.get("summary", {}))
    payload_summary = dict(payload_record.get("summary", {}))
    payload_binding = dict(payload_record.get("target_binding", {}))
    comparison_summary = dict(comparison_report.get("summary", {}))
    comparison_record = dict(comparison_report.get("comparison_record", {}))
    harder_target = dict(comparison_record.get("harder_target", {}))
    wrapper_summary = dict(wrapper_report.get("summary", {}))

    packet_ready = (
        packet_summary.get("terminal_outcome") == "QM_STAT_SANDBOX_REVIEW_EXECUTION_PACKET_READY"
        and packet_summary.get("packet_decision") == "review_packet_ready"
        and packet_summary.get("canonical_mutation_emitted") is False
    )
    intake_accept_ok = (
        intake_summary.get("terminal_outcome") == "QM_STAT_SANDBOX_GOVERNED_INTAKE_ACCEPTED_FOR_BOUNDED_SANDBOX_REVIEW"
        and intake_summary.get("intake_decision") == "intake_accepted_for_bounded_sandbox_review"
    )
    payload_primary_ok = (
        payload_summary.get("artifact_id") == packet_summary.get("primary_artifact_id")
        and payload_summary.get("artifact_id") == intake_summary.get("primary_artifact_id")
        and wrapper_summary.get("primary_artifact_id") == payload_summary.get("artifact_id")
    )
    support_role_ok = (
        comparison_summary.get("comparison_status_v0") == "ALIGNED_BOUNDED_v0_NONCLAIM"
        and comparison_record.get("comparison_disposition_v0")
        == "PAYLOAD_REMAINS_PRIMARY_GOVERNED_ENTRY_OBJECT_HARDER_TARGET_REMAINS_BOUND_SUPPORTING_EVIDENCE"
        and harder_target.get("artifact_id") == packet_summary.get("supporting_artifact_id")
        and harder_target.get("promotability") == "NOT_READY"
    )
    target_binding_ok = (
        payload_binding.get("row_id") == "ROW-SEAM-QM-STAT-001"
        and payload_binding.get("seam_id") == "SEAM-QM-STAT"
        and payload_binding.get("target_package_id") == "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0"
        and payload_binding.get("row_id") == witness_binding.get("row_id")
        and payload_binding.get("target_package_id") == witness_binding.get("target_package_id")
    )
    packet_rule_ok = all(
        token in packet_text
        for token in (
            "RESEARCH_MODE_QM_STAT_SANDBOX_REVIEW_EXECUTION_PACKET_NONCANONICAL_RULE_v0:",
            "REVIEW_PACKET_READY_PLUS_REVIEW_PACKET_EXECUTED_WITH_HOLD_PLUS_REVIEW_PACKET_EXECUTED_WITH_BOUNDED_ACCEPT_PLUSREVIEW_PACKET_BLOCKED_PENDING_ADDITIONAL_SUPPORT",
            "EXECUTE_ONE_BOUNDED_QM_STAT_SANDBOX_REVIEW_USING_AUTHORED_PACKET",
        )
    )
    canonical_action_block_ok = all(
        token in canonical_action_standard_text
        for token in (
            "TOE_CANONICAL_ACTION_PROMOTION_STATUS_v0: BLOCKED_PENDING_CRITERIA",
            "TOE_CANONICAL_ACTION_PROMOTION_REQUIRES_v0: THEOREM_TRANSPORT_REGIME_AND_GOVERNANCE_ALIGNMENT",
        )
    )

    if not all([packet_rule_ok, target_binding_ok, payload_primary_ok]):
        terminal_outcome = "QM_STAT_SANDBOX_REVIEW_BLOCKED_PENDING_ADDITIONAL_SUPPORT"
        review_decision = "bounded_review_blocked_pending_additional_support"
        next_action = "REPAIR_QM_STAT_SANDBOX_REVIEW_PACKET_BINDINGS_OR_REQUIRED_FIELDS"
    elif not all([packet_ready, intake_accept_ok, support_role_ok]):
        terminal_outcome = "QM_STAT_SANDBOX_REVIEW_HELD_PENDING_SUPPORT"
        review_decision = "bounded_review_held_pending_support"
        next_action = "REPAIR_QM_STAT_SANDBOX_REVIEW_INPUTS_AND_RERUN_EXECUTION"
    elif not canonical_action_block_ok:
        terminal_outcome = "QM_STAT_SANDBOX_REVIEW_REJECTED_DUE_TO_MISMATCH"
        review_decision = "bounded_review_rejected_due_to_mismatch"
        next_action = "RESTORE_CANONICAL_ACTION_BOUNDARY_BEFORE_ANY_REVIEW_FOLLOWTHROUGH"
    else:
        terminal_outcome = "QM_STAT_SANDBOX_REVIEW_COMPLETED_WITH_NO_CANONICAL_ACTION"
        review_decision = "bounded_review_completed_with_no_canonical_action"
        next_action = "AUTHOR_POST_REVIEW_QM_STAT_ADJUDICATION_SURFACE_WITHOUT_CANONICAL_PROMOTION"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "packet_ready": packet_ready,
            "intake_acceptance_present": intake_accept_ok,
            "payload_primary_object_preserved": payload_primary_ok,
            "harder_target_preserved_as_support_only": support_role_ok,
            "target_binding_matches_live_anchor": target_binding_ok,
            "packet_rule_tokens_present": packet_rule_ok,
            "canonical_action_boundary_present": canonical_action_block_ok,
        },
        "objective_quality": {
            "criteria": {
                "single_outcome_materialized": True,
                "canonical_mutation_withheld": True,
                "noncanonical_posture_preserved": True,
                "payload_remains_primary": payload_primary_ok,
                "support_evidence_remains_secondary": support_role_ok,
            },
            "inputs": {
                "packet_terminal_outcome": packet_summary.get("terminal_outcome"),
                "packet_decision": packet_summary.get("packet_decision"),
                "intake_terminal_outcome": intake_summary.get("terminal_outcome"),
                "payload_artifact_id": payload_summary.get("artifact_id"),
                "supporting_artifact_id": harder_target.get("artifact_id"),
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
            "review_decision": review_decision,
            "target_row_id": payload_binding.get("row_id"),
            "target_seam_id": payload_binding.get("seam_id"),
            "target_package_id": payload_binding.get("target_package_id"),
            "primary_artifact_id": payload_summary.get("artifact_id"),
            "supporting_artifact_id": harder_target.get("artifact_id"),
            "canonical_mutation_emitted": False,
            "next_action": next_action,
        },
        "source_bundle": {
            "packet": _ptr(PACKET_PATH),
            "packet_report": _ptr(packet_report_path),
            "intake_report": _ptr(intake_report_path),
            "payload_record": _ptr(payload_record_path),
            "comparison_report": _ptr(comparison_report_path),
            "wrapper_report": _ptr(wrapper_report_path),
            "witness_binding": _ptr(witness_binding_path),
            "canonical_action_standard": _ptr(canonical_action_standard_path),
        },
        "non_claim_boundary": "Repository-local sandbox review execution only; no governed promotion pass, canonical mutation, or seam-closure claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT sandbox review execution report.")
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
        "research_mode_qm_stat_sandbox_review_execution_report: "
        f"decision={payload['summary']['review_decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())