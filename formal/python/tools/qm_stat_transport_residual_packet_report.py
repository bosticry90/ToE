from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_TRANSPORT_RESIDUAL_PACKET_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "QM_STAT_TRANSPORT_RESIDUAL_PACKET_20260411_v0.json"
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


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    movement_policy = dict(declaration.get("movement_policy", {}))

    direct_attack_class_packet_report_path = REPO_ROOT / str(required_inputs.get("direct_attack_class_packet_report", ""))
    current_target_artifact_path = REPO_ROOT / str(required_inputs.get("current_target_artifact", ""))
    prior_target_artifact_path = REPO_ROOT / str(required_inputs.get("prior_target_artifact", ""))
    target_gate_path = REPO_ROOT / str(required_inputs.get("target_gate_path", ""))
    trend_report_path = REPO_ROOT / str(required_inputs.get("trend_report", ""))
    row_outcome_trend_path = REPO_ROOT / str(required_inputs.get("row_outcome_trend_report", ""))
    ledger_report_path = REPO_ROOT / str(required_inputs.get("ledger_report", ""))
    closure_map_report_path = REPO_ROOT / str(required_inputs.get("closure_map_report", ""))

    direct_attack_class_packet_report = _read_json(direct_attack_class_packet_report_path)
    current_target_artifact = _read_json(current_target_artifact_path)
    prior_target_artifact = _read_json(prior_target_artifact_path)
    trend_report = _read_json(trend_report_path)
    row_outcome_trend = _read_json(row_outcome_trend_path)
    ledger_report = _read_json(ledger_report_path)
    closure_map_report = _read_json(closure_map_report_path)

    row_id = str(declaration.get("row_id", "")).strip()
    target_package_id = str(declaration.get("target_package_id", "")).strip()
    packet_id = str(declaration.get("packet_id", "")).strip()

    direct_summary = dict(direct_attack_class_packet_report.get("summary", {}))
    direct_target = dict(direct_attack_class_packet_report.get("single_bounded_target", {}))
    selected_target_row = str(direct_summary.get("selected_target_row", "")).strip()
    selected_target_package_id = str(direct_summary.get("selected_target_package_id", "")).strip()

    mappings = list(closure_map_report.get("mappings", []))
    target_mapping = next((m for m in mappings if str(m.get("row_id", "")).strip() == row_id), None)

    prior = dict(trend_report.get("blocker_counts", {}).get("prior", {}))
    current = dict(trend_report.get("blocker_counts", {}).get("current", {}))
    seam_prior = int(prior.get("SEAM_INTEGRATION_GAP", 0) or 0)
    seam_current = int(current.get("SEAM_INTEGRATION_GAP", seam_prior) or 0)
    seam_delta = seam_current - seam_prior
    theorem_prior = int(prior.get("THEOREM_GAP", 0) or 0)
    theorem_current = int(current.get("THEOREM_GAP", theorem_prior) or 0)
    theorem_delta = theorem_current - theorem_prior

    row_counts = row_outcome_trend.get("objective_quality", {}).get("inputs", {}).get("row_outcome_counts", {})
    global_row_success_count = (
        sum(int((v or {}).get("success", 0) or 0) for v in row_counts.values()) if isinstance(row_counts, dict) else 0
    )

    current_adjudication = str(current_target_artifact.get("adjudication", {}).get("value", "")).strip()
    prior_adjudication = str(prior_target_artifact.get("adjudication", {}).get("value", "")).strip()
    target_row_success_increment_gt_0 = (
        current_adjudication not in {"", "NOT_YET_DISCHARGED"}
        and current_adjudication != prior_adjudication
    )

    actual_blocker_state_change = str(ledger_report.get("actual_blocker_state_change", "")).strip()
    blocker_token_changed = actual_blocker_state_change not in {"", "NO_DELTA_DETECTED_ROUTE_TO_REWORK"}
    blocker_token_delta = 1 if blocker_token_changed else 0

    seam_integration_gap_delta_lt_0 = seam_delta < 0
    theorem_gap_delta_lt_0 = theorem_delta < 0
    all_movement_signals_false = not any(
        [
            seam_integration_gap_delta_lt_0,
            theorem_gap_delta_lt_0,
            target_row_success_increment_gt_0,
            blocker_token_changed,
        ]
    )

    execution_valid = (
        direct_summary.get("packet_outcome") == "DIRECT_MASTER_ACTION_ATTACK_CLASS_PACKET_MATERIALIZED"
        and selected_target_row == row_id
        and selected_target_package_id == target_package_id
        and target_mapping is not None
        and target_gate_path.exists()
        and str(current_target_artifact.get("seam_id", "")).strip() == "SEAM-QM-STAT"
        and str(current_target_artifact.get("status", "")).strip() != ""
    )

    if execution_valid and any(
        [
            seam_integration_gap_delta_lt_0,
            theorem_gap_delta_lt_0,
            target_row_success_increment_gt_0,
            blocker_token_changed,
        ]
    ):
        packet_classification = "QM_STAT_TRANSPORT_RESIDUAL_MOVED"
        next_action = "CONTINUE_DIRECT_MASTER_ACTION_ATTACK_CLASS"
    elif execution_valid and all_movement_signals_false:
        packet_classification = "QM_STAT_TRANSPORT_RESIDUAL_VALID_BUT_NONMOVING"
        next_action = "EMIT_QM_STAT_TRANSPORT_RESIDUAL_RULING"
    else:
        packet_classification = "QM_STAT_TRANSPORT_RESIDUAL_INCOMPLETE"
        next_action = "RESTORE_QM_STAT_PACKET_PRECONDITIONS_AND_REVIEW_ONCE"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "parent_attack_class_packet_materialized": direct_summary.get("packet_outcome")
            == "DIRECT_MASTER_ACTION_ATTACK_CLASS_PACKET_MATERIALIZED",
            "selected_target_row_matches_packet": selected_target_row == row_id,
            "selected_target_package_matches_packet": selected_target_package_id == target_package_id,
            "closure_map_contains_target_row": target_mapping is not None,
            "target_gate_present": target_gate_path.exists(),
            "current_target_artifact_present": current_target_artifact_path.exists(),
            "execution_valid": execution_valid,
        },
        "objective_quality": {
            "criteria": {
                "seam_integration_gap_delta_lt_0": seam_integration_gap_delta_lt_0,
                "theorem_gap_delta_lt_0": theorem_gap_delta_lt_0,
                "target_row_success_increment_gt_0": target_row_success_increment_gt_0,
                "blocker_token_changed": blocker_token_changed,
                "all_movement_signals_false": all_movement_signals_false,
                "packet_classification_materialized": packet_classification in {
                    "QM_STAT_TRANSPORT_RESIDUAL_MOVED",
                    "QM_STAT_TRANSPORT_RESIDUAL_VALID_BUT_NONMOVING",
                    "QM_STAT_TRANSPORT_RESIDUAL_INCOMPLETE",
                },
            },
            "inputs": {
                "packet_id": packet_id,
                "row_id": row_id,
                "target_package_id": target_package_id,
                "seam_integration_gap_prior": seam_prior,
                "seam_integration_gap_current": seam_current,
                "seam_integration_gap_delta": seam_delta,
                "theorem_gap_prior": theorem_prior,
                "theorem_gap_current": theorem_current,
                "theorem_gap_delta": theorem_delta,
                "global_row_success_count": global_row_success_count,
                "prior_target_artifact_adjudication": prior_adjudication,
                "current_target_artifact_adjudication": current_adjudication,
                "actual_blocker_state_change": actual_blocker_state_change,
                "blocker_token_delta": blocker_token_delta,
                "movement_signals": {
                    "seam_integration_gap_delta_lt_0": seam_integration_gap_delta_lt_0,
                    "theorem_gap_delta_lt_0": theorem_gap_delta_lt_0,
                    "target_row_success_increment_gt_0": target_row_success_increment_gt_0,
                    "blocker_token_changed": blocker_token_changed,
                },
                "success_rule": movement_policy.get("success_rule"),
                "failure_rule": movement_policy.get("failure_rule"),
                "no_loop_rule": movement_policy.get("no_loop_rule"),
                "immediate_ruling_required": movement_policy.get("immediate_ruling_required"),
            },
            "summary": {
                "all_criteria_satisfied": packet_classification != "QM_STAT_TRANSPORT_RESIDUAL_INCOMPLETE",
                "phase_status": (
                    "COMPLETE"
                    if packet_classification != "QM_STAT_TRANSPORT_RESIDUAL_INCOMPLETE"
                    else "INCOMPLETE"
                ),
                "next_action": next_action,
            },
        },
        "summary": {
            "packet_id": packet_id,
            "row_id": row_id,
            "target_package_id": target_package_id,
            "packet_classification": packet_classification,
            "seam_integration_gap_delta": seam_delta,
            "theorem_gap_delta": theorem_delta,
            "target_row_success_increment_gt_0": target_row_success_increment_gt_0,
            "blocker_token_delta": blocker_token_delta,
            "success_rule": movement_policy.get("success_rule"),
            "failure_rule": movement_policy.get("failure_rule"),
            "no_loop_rule": movement_policy.get("no_loop_rule"),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "direct_attack_class_packet_report": _ptr(direct_attack_class_packet_report_path),
            "current_target_artifact": _ptr(current_target_artifact_path),
            "prior_target_artifact": _ptr(prior_target_artifact_path),
            "target_gate_path": _ptr(target_gate_path),
            "trend_report": _ptr(trend_report_path),
            "row_outcome_trend_report": _ptr(row_outcome_trend_path),
            "ledger_report": _ptr(ledger_report_path),
            "closure_map_report": _ptr(closure_map_report_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT transport/residual packet report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate QM-STAT transport/residual packet report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_transport_residual_packet_20260411_v0.json",
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
        "qm_stat_transport_residual_packet_report: "
        f"classification={payload['summary']['packet_classification']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
