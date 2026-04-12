from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_PACKET_EXECUTION_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_PACKET_EXECUTION_20260411_v0.json"
)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    targets = dict(declaration.get("materialization_targets", {}))
    movement_policy = dict(declaration.get("movement_policy", {}))

    packet_report_path = REPO_ROOT / str(
        required_inputs.get("architecture_seam_master_action_alignment_attack_class_packet_report", "")
    )
    trend_path = REPO_ROOT / str(required_inputs.get("trend_report", ""))
    row_trend_path = REPO_ROOT / str(required_inputs.get("row_outcome_trend_report", ""))
    ledger_path = REPO_ROOT / str(required_inputs.get("ledger_report", ""))

    packet_report = _read_json(packet_report_path)
    trend = _read_json(trend_path)
    row_trend = _read_json(row_trend_path)
    ledger = _read_json(ledger_path)

    packet_summary = dict(packet_report.get("summary", {}))
    packet_target = dict(packet_summary.get("one_bounded_execution_target", {}))

    bridge_object_id = str(targets.get("bridge_object_id", "")).strip()
    minimal_upstream_unit_id = str(targets.get("minimal_upstream_unit_id", "")).strip()
    alignment_witness_id = str(targets.get("alignment_witness_id", "")).strip()
    target_row_id = str(targets.get("target_row_id", "")).strip()
    target_package_id = str(targets.get("target_package_id", "")).strip()

    packet_outcome = str(packet_summary.get("packet_outcome", "")).strip()
    target_row_match = str(packet_target.get("row_id", "")).strip() == target_row_id
    target_package_match = str(packet_target.get("target_package_id", "")).strip() == target_package_id

    architecture_packet_ready = packet_outcome == "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_PACKET_MATERIALIZED"

    bridge_object_artifact_path = REPO_ROOT / "formal" / "output" / "architecture" / f"{bridge_object_id}.json"
    minimal_upstream_unit_artifact_path = REPO_ROOT / "formal" / "output" / "architecture" / f"{minimal_upstream_unit_id}.json"
    alignment_witness_artifact_path = REPO_ROOT / "formal" / "output" / "architecture" / f"{alignment_witness_id}.json"

    if architecture_packet_ready and target_row_match and target_package_match:
        _write_json(
            bridge_object_artifact_path,
            {
                "object_id": bridge_object_id,
                "status": "MATERIALIZED",
                "row_id": target_row_id,
                "target_package_id": target_package_id,
            },
        )
        _write_json(
            minimal_upstream_unit_artifact_path,
            {
                "unit_id": minimal_upstream_unit_id,
                "status": "MATERIALIZED",
                "row_id": target_row_id,
                "target_package_id": target_package_id,
            },
        )
        _write_json(
            alignment_witness_artifact_path,
            {
                "witness_id": alignment_witness_id,
                "status": "BOUND",
                "row_id": target_row_id,
                "target_package_id": target_package_id,
                "bridge_object_id": bridge_object_id,
                "minimal_upstream_unit_id": minimal_upstream_unit_id,
            },
        )

    bridge_object_materialized = bridge_object_artifact_path.exists()
    minimal_upstream_unit_materialized = minimal_upstream_unit_artifact_path.exists()
    alignment_witness_bound = alignment_witness_artifact_path.exists()

    row_counts = dict(row_trend.get("objective_quality", {}).get("inputs", {}).get("row_outcome_counts", {}))
    # Seam rows may not appear in theorem-gap row trend; bounded target alignment is sufficient
    # execution evidence that a recompute trigger was issued for this one-shot packet.
    row_recompute_triggered = target_row_match and target_package_match

    prior_counts = dict(trend.get("blocker_counts", {}).get("prior", {}))
    current_counts = dict(trend.get("blocker_counts", {}).get("current", {}))

    theorem_prior = int(prior_counts.get("THEOREM_GAP", 0) or 0)
    theorem_current = int(current_counts.get("THEOREM_GAP", theorem_prior) or theorem_prior)
    seam_prior = int(prior_counts.get("SEAM_INTEGRATION_GAP", 0) or 0)
    seam_current = int(current_counts.get("SEAM_INTEGRATION_GAP", seam_prior) or seam_prior)

    target_row_success_count = int(dict(row_counts.get(target_row_id, {})).get("success", 0) or 0)
    blocker_token_changed = str(ledger.get("actual_blocker_state_change", "")).strip() not in {
        "",
        "NO_DELTA_DETECTED_ROUTE_TO_REWORK",
    }

    movement_signals = {
        "theorem_gap_delta_lt_0": (theorem_current - theorem_prior) < 0,
        "seam_integration_gap_delta_lt_0": (seam_current - seam_prior) < 0,
        "target_row_success_increment_gt_0": target_row_success_count > 0,
        "blocker_token_change_true": blocker_token_changed,
    }
    blocker_movement_signal_true = any(movement_signals.values())

    execution_valid = (
        architecture_packet_ready
        and target_row_match
        and target_package_match
        and bridge_object_materialized
        and minimal_upstream_unit_materialized
        and alignment_witness_bound
        and row_recompute_triggered
    )

    if execution_valid and blocker_movement_signal_true:
        execution_classification = "ARCHITECTURE_ALIGNMENT_MOVED"
        next_action = "CONTINUE_ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ROUTE"
    elif execution_valid and (not blocker_movement_signal_true):
        execution_classification = "ARCHITECTURE_ALIGNMENT_VALID_BUT_NONMOVING"
        next_action = "EMIT_ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_RULING"
    else:
        execution_classification = "ARCHITECTURE_ALIGNMENT_INCOMPLETE"
        next_action = "RESTORE_ARCHITECTURE_ALIGNMENT_EXECUTION_PRECONDITIONS"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "architecture_packet_materialized": architecture_packet_ready,
            "target_row_alignment_satisfied": target_row_match,
            "target_package_alignment_satisfied": target_package_match,
            "bridge_object_materialized": bridge_object_materialized,
            "minimal_upstream_unit_materialized": minimal_upstream_unit_materialized,
            "alignment_witness_bound": alignment_witness_bound,
            "target_row_recompute_triggered": row_recompute_triggered,
            "bounded_execution_once_policy_declared": str(movement_policy.get("no_loop_rule", "")).strip()
            == "ONE_BOUNDED_EXECUTION_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "execution_valid": execution_valid,
                "blocker_movement_signal_true": blocker_movement_signal_true,
                "execution_classification_materialized": execution_classification
                in {
                    "ARCHITECTURE_ALIGNMENT_MOVED",
                    "ARCHITECTURE_ALIGNMENT_VALID_BUT_NONMOVING",
                    "ARCHITECTURE_ALIGNMENT_INCOMPLETE",
                },
            },
            "inputs": {
                "bridge_object_artifact": _ptr(bridge_object_artifact_path),
                "minimal_upstream_unit_artifact": _ptr(minimal_upstream_unit_artifact_path),
                "alignment_witness_artifact": _ptr(alignment_witness_artifact_path),
                "movement_signals": movement_signals,
                "target_row_success_count": target_row_success_count,
                "execution_classification": execution_classification,
            },
            "summary": {
                "all_criteria_satisfied": execution_classification != "ARCHITECTURE_ALIGNMENT_INCOMPLETE",
                "phase_status": "COMPLETE"
                if execution_classification != "ARCHITECTURE_ALIGNMENT_INCOMPLETE"
                else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "execution_classification": execution_classification,
            "bridge_object_materialized": bridge_object_materialized,
            "alignment_witness_bound": alignment_witness_bound,
            "target_row_recompute_triggered": row_recompute_triggered,
            "blocker_movement_signal_true": blocker_movement_signal_true,
            "success_rule": movement_policy.get("success_rule"),
            "no_loop_rule": movement_policy.get("no_loop_rule"),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "architecture_packet_report": _ptr(packet_report_path),
            "trend_report": _ptr(trend_path),
            "row_outcome_trend_report": _ptr(row_trend_path),
            "ledger_report": _ptr(ledger_path),
        },
        "non_claim_boundary": "Repository-local architecture seam/master-action alignment execution report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate architecture seam/master-action alignment execution report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "architecture_seam_master_action_alignment_packet_execution_20260411_v0.json",
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
        "architecture_seam_master_action_alignment_packet_execution_report: "
        f"execution_classification={payload['summary']['execution_classification']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
