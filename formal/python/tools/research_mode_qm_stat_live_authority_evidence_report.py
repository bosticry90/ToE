from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "RESEARCH_MODE_QM_STAT_LIVE_AUTHORITY_EVIDENCE_REPORT_20260419_v0"
DEFAULT_OUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "research_mode_qm_stat_live_authority_evidence_20260419_v0.json"
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


def _latest_active_definition(entries: list[dict[str, Any]], row_id: str) -> dict[str, Any]:
    active_entries = [
        entry
        for entry in entries
        if entry.get("target_row_id") == row_id and entry.get("status") == "ACTIVE"
    ]
    return dict(active_entries[-1]) if active_entries else {}


def build_report(*, captured_at_utc: str | None) -> dict[str, Any]:
    adjudication_report_path = REPO_ROOT / "formal/output/reports/research_mode_qm_stat_post_review_adjudication_20260419_v0.json"
    harder_target_report_path = REPO_ROOT / "formal/output/reports/research_mode_harder_qm_stat_target_20260419_v0.json"
    comparison_report_path = REPO_ROOT / "formal/output/reports/research_mode_qm_stat_sandbox_candidate_comparison_20260419_v0.json"
    payload_record_path = REPO_ROOT / "formal/output/reports/research_mode_qm_stat_sandbox_payload_record_20260419_v0.json"
    bridge_object_path = REPO_ROOT / "formal/output/architecture/SEAM_TO_MASTER_ACTION_RESIDUAL_BRIDGE_OBJECT_v0.json"
    witness_binding_path = REPO_ROOT / "formal/output/architecture/SEAM_QM_STAT_TRANSPORT_WITNESS_BINDING_v0.json"
    blocker_definitions_path = REPO_ROOT / "formal/output/authority/authoritative_blocker_definitions.json"

    adjudication_report = _read_json(adjudication_report_path)
    harder_target_report = _read_json(harder_target_report_path)
    comparison_report = _read_json(comparison_report_path)
    payload_record = _read_json(payload_record_path)
    bridge_object = _read_json(bridge_object_path)
    witness_binding = _read_json(witness_binding_path)
    blocker_definitions = _read_json(blocker_definitions_path)

    adjudication_summary = dict(adjudication_report.get("summary", {}))
    harder_target_artifact = dict(harder_target_report.get("artifact", {}))
    harder_metrics = dict(harder_target_artifact.get("metrics", {}))
    harder_live_anchor = dict(harder_target_artifact.get("live_anchor", {}))
    comparison_summary = dict(comparison_report.get("summary", {}))
    comparison_criteria = dict(comparison_report.get("objective_quality", {}).get("criteria", {}))
    payload_binding = dict(payload_record.get("target_binding", {}))
    latest_definition = _latest_active_definition(
        list(blocker_definitions.get("entries", [])), str(payload_binding.get("row_id", ""))
    )

    adjudication_hold_ok = (
        adjudication_summary.get("post_review_adjudication") == "RETAIN_AS_BOUNDED_REVIEWED_CANDIDATE"
        and adjudication_summary.get("candidate_disposition") == "RETAIN_BOUNDED_REVIEWED_CANDIDATE"
        and adjudication_summary.get("canonical_mutation_emitted") is False
    )
    live_anchor_alignment_ok = all(
        [
            payload_binding.get("row_id") == bridge_object.get("row_id"),
            payload_binding.get("row_id") == witness_binding.get("row_id"),
            payload_binding.get("target_package_id") == bridge_object.get("target_package_id"),
            harder_live_anchor.get("row_id") == payload_binding.get("row_id"),
            harder_live_anchor.get("target_package_id") == payload_binding.get("target_package_id"),
            harder_live_anchor.get("bridge_object_id") == bridge_object.get("object_id"),
            harder_live_anchor.get("witness_id") == witness_binding.get("witness_id"),
        ]
    )
    harder_target_strength_ok = all(
        [
            comparison_summary.get("comparison_status_v0") == "ALIGNED_BOUNDED_v0_NONCLAIM",
            comparison_criteria.get("harder_metric_ok") is True,
            float(harder_metrics.get("continuity_residual_sup_abs_max", 1.0)) < 1.0e-6,
            float(harder_metrics.get("mass_drift_abs_max", 1.0)) < 1.0e-6,
            float(harder_metrics.get("first_moment_transport_gap_abs_max", 1.0)) < 1.0e-5,
            float(harder_metrics.get("second_moment_transport_gap_abs_max", 1.0)) < 1.0e-4,
        ]
    )
    authority_binding_ok = all(
        [
            latest_definition.get("definition_id") == "REVISED_BLOCKER_DEFINITION_20260411_v0",
            latest_definition.get("coupling_state") == "TIGHTENED",
            latest_definition.get("promotion_ruling") == "COUPLING_REFINEMENT_SUPPORTS_AUTHORITY_PROMOTION",
            harder_live_anchor.get("authoritative_blocker_definition_id") == latest_definition.get("definition_id"),
            harder_live_anchor.get("authoritative_coupling_state") == latest_definition.get("coupling_state"),
            harder_live_anchor.get("authoritative_promotion_ruling") == latest_definition.get("promotion_ruling"),
        ]
    )
    reentry_evidence_ready = all(
        [adjudication_hold_ok, live_anchor_alignment_ok, harder_target_strength_ok, authority_binding_ok]
    )

    terminal_outcome = (
        "QM_STAT_STRONGER_LIVE_AUTHORITY_EVIDENCE_MATERIALIZED"
        if reentry_evidence_ready
        else "QM_STAT_STRONGER_LIVE_AUTHORITY_EVIDENCE_INCOMPLETE"
    )
    next_action = (
        "REENTER_QM_STAT_BOUNDED_REVIEW_ONLY_IF_NEW_SUPPORTING_EVIDENCE_MATERIALIZES"
        if reentry_evidence_ready
        else "AUTHOR_ONE_ADDITIONAL_LIVE_TARGET_SUPPORT_SURFACE_BEFORE_REENTRY"
    )

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "post_review_hold_state_present": adjudication_hold_ok,
            "live_anchor_alignment": live_anchor_alignment_ok,
            "harder_target_strength_preserved": harder_target_strength_ok,
            "authority_binding_strengthened": authority_binding_ok,
            "reentry_evidence_ready": reentry_evidence_ready,
        },
        "objective_quality": {
            "criteria": {
                "single_outcome_materialized": True,
                "payload_binding_preserved": live_anchor_alignment_ok,
                "support_evidence_remains_secondary": comparison_criteria.get("support_role_ok") is True,
                "canonical_mutation_withheld": True,
                "future_reentry_supported": reentry_evidence_ready,
            },
            "inputs": {
                "post_review_adjudication": adjudication_summary.get("post_review_adjudication"),
                "target_row_id": payload_binding.get("row_id"),
                "target_seam_id": payload_binding.get("seam_id"),
                "target_package_id": payload_binding.get("target_package_id"),
                "bridge_object_id": bridge_object.get("object_id"),
                "witness_id": witness_binding.get("witness_id"),
                "authoritative_blocker_definition_id": latest_definition.get("definition_id"),
                "continuity_residual_sup_abs_max": harder_metrics.get("continuity_residual_sup_abs_max"),
                "first_moment_transport_gap_abs_max": harder_metrics.get("first_moment_transport_gap_abs_max"),
                "second_moment_transport_gap_abs_max": harder_metrics.get("second_moment_transport_gap_abs_max"),
            },
            "summary": {
                "all_criteria_satisfied": reentry_evidence_ready,
                "phase_status": "COMPLETE" if reentry_evidence_ready else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_row_id": payload_binding.get("row_id"),
            "target_seam_id": payload_binding.get("seam_id"),
            "target_package_id": payload_binding.get("target_package_id"),
            "authoritative_blocker_definition_id": latest_definition.get("definition_id"),
            "canonical_mutation_emitted": False,
            "next_action": next_action,
        },
        "source_bundle": {
            "post_review_adjudication_report": _ptr(adjudication_report_path),
            "harder_target_report": _ptr(harder_target_report_path),
            "comparison_report": _ptr(comparison_report_path),
            "payload_record": _ptr(payload_record_path),
            "bridge_object": _ptr(bridge_object_path),
            "witness_binding": _ptr(witness_binding_path),
            "blocker_definitions": _ptr(blocker_definitions_path),
        },
        "non_claim_boundary": "Repository-local stronger live-target or authority evidence only; no canonical promotion, canonical mutation, or seam-closure claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT stronger live-target or authority-evidence report.")
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
        "research_mode_qm_stat_live_authority_evidence_report: "
        f"outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())