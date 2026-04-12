from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PACKET41_NUMERIC_CLEARANCE_REWORK_TRANCHE_20260411_v0"

CYCLE02_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "toe_qft_gr_seam_packet41_reconsideration_scorecard_evaluation_cycle02_checkpoint_v0.json"
)
PACKET41_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "packet41_successor_decision_enforcement_20260411_v0.json"
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


def build_report(captured_at_utc: str | None) -> dict[str, Any]:
    cycle02 = _read_json(CYCLE02_PATH)
    packet41 = _read_json(PACKET41_REPORT_PATH)

    payload = cycle02.get("payload", {})
    score = payload.get("scorecard_values", {})
    thresholds = payload.get("threshold_pass", {})
    review_layer = payload.get("review_layer_pass", {})

    s_value = float(score.get("S_value", 0.0) or 0.0)
    m_value = float(score.get("M_value", 0.0) or 0.0)
    streak3 = int(score.get("Streak3_value", 0) or 0)

    threshold_1_margin = s_value - 0.12
    threshold_2_margin = m_value - 0.18
    threshold_3_margin = 1 - streak3

    review_flags = [
        bool(review_layer.get("packet41_eligibility_review_pass", False)),
        bool(review_layer.get("packet41_targeted_justification_review_pass", False)),
        bool(review_layer.get("packet41_hold_fork_release_condition_pass", False)),
        bool(review_layer.get("retrospective_cumulative_delta_audit_release_condition_pass", False)),
    ]
    review_layer_pass_count = sum(1 for v in review_flags if v)
    review_layer_required_count = 4
    review_layer_clearance_ratio = review_layer_pass_count / review_layer_required_count
    review_layer_clearance_gap = review_layer_required_count - review_layer_pass_count

    actionable_parameter = {
        "name": "review_layer_pass_count",
        "current_value": review_layer_pass_count,
        "target_value": review_layer_required_count,
        "gap": review_layer_clearance_gap,
        "normalized_gap": round(1.0 - review_layer_clearance_ratio, 6),
        "reason": "Threshold-4 gate is blocked only by uncleared review-layer stack while thresholds 1-3 are already cleared.",
    }

    packet41_inputs = packet41.get("objective_quality", {}).get("inputs", {})
    cycle02_outcome = str(packet41_inputs.get("cycle02_outcome", ""))
    hold_state_changed = "PROMOTABLE" in cycle02_outcome or "REJECTED" in cycle02_outcome

    criteria = {
        "threshold_1_already_clear": bool(thresholds.get("threshold_1_pass", False)),
        "threshold_2_already_clear": bool(thresholds.get("threshold_2_pass", False)),
        "threshold_3_already_clear": bool(thresholds.get("threshold_3_pass", False)),
        "threshold_4_blocked_by_review_layer": (
            bool(thresholds.get("threshold_4_pass", False)) is False
            and str(thresholds.get("auto_fail_reason", "")) == "REVIEW_LAYER_STACK_NOT_CLEARED_v0"
        ),
        "single_actionable_parameter_isolated": actionable_parameter["gap"] > 0,
    }

    success_criteria = {
        "packet41_hold_state_changed": hold_state_changed,
        "review_layer_clearance_gap_reduced": actionable_parameter["gap"] < 4,
    }

    outcome = "SUCCESS" if any(success_criteria.values()) else "NO_CHANGE"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "target": "QFT_GR_PACKET41_NUMERIC_CLEARANCE",
        "expected_blocker_state_change": "PACKET41_HOLD_TO_CLEARED_OR_SHARPER_FAILED",
        "criteria": criteria,
        "actionable_parameter": actionable_parameter,
        "numeric_margins": {
            "threshold_1_margin_s_minus_0p12": round(threshold_1_margin, 10),
            "threshold_2_margin_m_minus_0p18": round(threshold_2_margin, 10),
            "threshold_3_margin_1_minus_streak3": threshold_3_margin,
            "review_layer_clearance_ratio": round(review_layer_clearance_ratio, 6),
        },
        "success_criteria": success_criteria,
        "summary": {
            "outcome": outcome,
            "packet41_hold_state_changed": hold_state_changed,
            "next_action": (
                "RECOMPUTE_BLOCKER_STATE"
                if outcome == "SUCCESS"
                else "SWITCH_TO_QM_MICRO_SUBTARGET_REFINEMENT"
            ),
        },
        "source_bundle": {
            "cycle02_scorecard": _ptr(CYCLE02_PATH),
            "packet41_enforcement_report": _ptr(PACKET41_REPORT_PATH),
        },
        "non_claim_boundary": "Repository-local Packet41 numeric-clearance rework tranche artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate Packet41 narrow numeric-clearance rework tranche report.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "packet41_numeric_clearance_rework_tranche_20260411_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "packet41_numeric_clearance_rework_tranche_report: "
        f"outcome={payload['summary']['outcome']} "
        f"out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())