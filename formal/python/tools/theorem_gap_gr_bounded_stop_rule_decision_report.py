from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "THEOREM_GAP_GR_BOUNDED_STOP_RULE_DECISION_20260411_v0"

GR_SUBTARGET_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_gr_subtarget_tranche_20260411_v0.json"
)
CLOSURE_MAP_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_closure_map_20260410_v0.json"
)

TARGET_ROW = "ROW-PILLAR-GR-001"
MAX_NO_CHANGE_ATTEMPTS = 1
EXCLUDED_ROWS = {"ROW-PILLAR-QM-001", "ROW-PILLAR-GR-001"}
PREFERRED_ORDER = [
    "ROW-PILLAR-STAT-001",
    "ROW-PILLAR-COSMO-001",
    "ROW-PILLAR-EM-001",
    "ROW-PILLAR-QFT-001",
    "ROW-PILLAR-SR-001",
    "ROW-SEAM-QFT-GR-001",
    "ROW-SEAM-QM-STAT-001",
    "ROW-SEAM-COSMO-SR-001",
]


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


def _pick_next_lane(mappings: list[dict[str, Any]]) -> dict[str, Any] | None:
    by_row = {str(m.get("row_id", "")): m for m in mappings}
    for row_id in PREFERRED_ORDER:
        candidate = by_row.get(row_id)
        if candidate is None:
            continue
        if row_id in EXCLUDED_ROWS:
            continue
        if str(candidate.get("blocker_class", "")) in {"THEOREM_GAP", "SEAM_INTEGRATION_GAP", "PARITY_DRIFT"}:
            return candidate
    for candidate in mappings:
        row_id = str(candidate.get("row_id", ""))
        if row_id in EXCLUDED_ROWS:
            continue
        if str(candidate.get("blocker_class", "")) in {"THEOREM_GAP", "SEAM_INTEGRATION_GAP", "PARITY_DRIFT"}:
            return candidate
    return None


def build_report(captured_at_utc: str | None, consume_attempt: bool) -> dict[str, Any]:
    gr = _read_json(GR_SUBTARGET_REPORT_PATH)
    closure_map = _read_json(CLOSURE_MAP_PATH)

    gr_inputs = gr.get("objective_quality", {}).get("inputs", {})
    theorem_gap_delta = int(gr_inputs.get("theorem_gap_delta", 0) or 0)
    target_row_success_incremented = bool(gr_inputs.get("target_row_success_count_incremented", False))
    movement_observed = theorem_gap_delta < 0 or target_row_success_incremented

    no_change_streak = 0
    if not movement_observed:
        no_change_streak = 1 if consume_attempt else 0

    stop_rule_triggered = (not movement_observed) and (no_change_streak >= MAX_NO_CHANGE_ATTEMPTS)
    selected_next_lane = _pick_next_lane(list(closure_map.get("mappings", [])))

    if stop_rule_triggered:
        decision = "DEFER_OR_RECLASSIFY_GR_NEAR_TERM_BLOCKER_BURN_LANE"
        next_action = "SELECT_NEXT_NON_QM_NON_GR_BLOCKER_BEARING_LANE"
    else:
        decision = "CONTINUE_GR_ON_NARROWER_SUBPROBLEM"
        next_action = "RUN_GR_NARROW_SUBPROBLEM_BLOCKER_MOVING_TRANCHE"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "target": "GR_ACTIVE_LANE_PROBATION_AND_BOUNDED_STOP_RULE",
        "inputs": {
            "target_row": TARGET_ROW,
            "theorem_gap_delta": theorem_gap_delta,
            "target_row_success_count_incremented": target_row_success_incremented,
            "max_no_change_attempts": MAX_NO_CHANGE_ATTEMPTS,
            "effective_no_change_streak": no_change_streak,
            "consume_attempt": consume_attempt,
            "movement_observed": movement_observed,
        },
        "summary": {
            "decision": decision,
            "gr_continuation_earned": movement_observed,
            "stop_rule_triggered": stop_rule_triggered,
            "next_action": next_action,
            "selected_next_lane": (
                {
                    "row_id": selected_next_lane.get("row_id"),
                    "domain": selected_next_lane.get("domain"),
                    "blocker_class": selected_next_lane.get("blocker_class"),
                    "owning_lane": selected_next_lane.get("owning_lane"),
                    "closure_gate": selected_next_lane.get("closure_gate"),
                    "required_closure_artifact": selected_next_lane.get("required_closure_artifact"),
                }
                if selected_next_lane is not None
                else None
            ),
            "failure_diagnosis": (
                "NO_THEOREM_GAP_DELTA_CHANGE_AND_NO_ROW_SUCCESS_INCREMENT"
                if not movement_observed
                else None
            ),
        },
        "source_bundle": {
            "gr_subtarget_report": _ptr(GR_SUBTARGET_REPORT_PATH),
            "closure_map": _ptr(CLOSURE_MAP_PATH),
        },
        "non_claim_boundary": "Repository-local GR bounded stop-rule decision artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate theorem-gap GR bounded stop-rule decision report.")
    parser.add_argument("--consume-attempt", action="store_true")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_gr_bounded_stop_rule_decision_20260411_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(ns.captured_at_utc, consume_attempt=bool(ns.consume_attempt))
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "theorem_gap_gr_bounded_stop_rule_decision_report: "
        f"decision={payload['summary']['decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
