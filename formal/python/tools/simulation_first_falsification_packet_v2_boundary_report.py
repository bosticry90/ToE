from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SIMULATION_FIRST_FALSIFICATION_PACKET_REPORT_20260411_v2"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SIMULATION_FIRST_FALSIFICATION_PACKET_20260411_v2.json"
)
TREND_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json"
ROW_TREND_PATH = REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_row_outcome_trend_20260411_v0.json"

ROW_RE = re.compile(r"^\|\s*Bragg\s+(condition_[AB])\s*\|.*\|\s*(PASS|FAIL)\s*\|\s*$", re.IGNORECASE)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _extract_counts(md_text: str) -> dict[str, dict[str, int]]:
    out = {
        "condition_A": {"PASS": 0, "FAIL": 0},
        "condition_B": {"PASS": 0, "FAIL": 0},
    }
    for line in md_text.splitlines():
        m = ROW_RE.match(line.strip())
        if not m:
            continue
        condition = m.group(1)
        result = m.group(2).upper()
        out[condition][result] += 1
    return out


def _rate(numerator: int, denominator: int) -> float:
    if denominator <= 0:
        return 0.0
    return numerator / denominator


def build_report(*, declaration_path: Path, cross_anchor_report_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    trend = _read_json(TREND_PATH)
    row_trend = _read_json(ROW_TREND_PATH)
    md = _read_text(cross_anchor_report_path)

    counts = _extract_counts(md)
    a_pass = counts["condition_A"]["PASS"]
    a_fail = counts["condition_A"]["FAIL"]
    b_pass = counts["condition_B"]["PASS"]
    b_fail = counts["condition_B"]["FAIL"]

    a_total = a_pass + a_fail
    b_total = b_pass + b_fail
    total = a_total + b_total

    pass_rate_a = _rate(a_pass, a_total)
    pass_rate_b = _rate(b_pass, b_total)
    fail_rate_a = _rate(a_fail, a_total)
    fail_rate_b = _rate(b_fail, b_total)

    boundary_sharpness = pass_rate_a - pass_rate_b
    policy = declaration.get("boundary_mapping_policy", {})
    min_sharpness = float(policy.get("minimum_sharpness_for_usable_boundary", 0.5) or 0.5)

    condition_b_is_limiter = fail_rate_b > fail_rate_a
    usable_boundary_mapped = total > 0 and boundary_sharpness >= min_sharpness and condition_b_is_limiter

    theorem_prior = int(trend.get("blocker_counts", {}).get("prior", {}).get("THEOREM_GAP", 0))
    theorem_current = int(trend.get("blocker_counts", {}).get("current", {}).get("THEOREM_GAP", theorem_prior))
    theorem_delta = theorem_current - theorem_prior
    row_counts = row_trend.get("objective_quality", {}).get("inputs", {}).get("row_outcome_counts", {})
    global_row_success = sum(int((v or {}).get("success", 0) or 0) for v in row_counts.values()) if isinstance(row_counts, dict) else 0
    blocker_facing_movement = theorem_delta < 0 or global_row_success > 0

    if total == 0:
        packet_outcome = "INCONCLUSIVE_INSUFFICIENT_ROWS"
        scientific_state_change = False
    elif usable_boundary_mapped:
        packet_outcome = "BOUNDARY_MAPPED_CONDITION_B_LIMITER_CONFIRMED"
        scientific_state_change = True
    elif condition_b_is_limiter:
        packet_outcome = "PARTIAL_BOUNDARY_SIGNAL_CONDITION_B_LIMITER"
        scientific_state_change = True
    else:
        packet_outcome = "NO_BOUNDARY_SIGNAL"
        scientific_state_change = False

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "campaign_id": declaration.get("campaign_id"),
        "packet_id": declaration.get("packet_id"),
        "criteria": {
            "cross_anchor_report_exists": cross_anchor_report_path.exists(),
            "comparison_rows_present": total > 0,
            "condition_split_materialized": a_total > 0 and b_total > 0,
            "boundary_sharpness_metric_materialized": True,
        },
        "objective_quality": {
            "criteria": {
                "usable_boundary_mapped": usable_boundary_mapped,
                "condition_b_regime_limiter_confirmed": condition_b_is_limiter,
                "scientific_state_change_observed": scientific_state_change,
                "blocker_facing_movement_observed": blocker_facing_movement,
            },
            "inputs": {
                "condition_A_pass": a_pass,
                "condition_A_fail": a_fail,
                "condition_B_pass": b_pass,
                "condition_B_fail": b_fail,
                "pass_rate_condition_A": round(pass_rate_a, 6),
                "pass_rate_condition_B": round(pass_rate_b, 6),
                "fail_rate_condition_A": round(fail_rate_a, 6),
                "fail_rate_condition_B": round(fail_rate_b, 6),
                "boundary_sharpness": round(boundary_sharpness, 6),
                "minimum_sharpness_for_usable_boundary": min_sharpness,
                "theorem_gap_prior": theorem_prior,
                "theorem_gap_current": theorem_current,
                "theorem_gap_delta": theorem_delta,
                "global_row_success_count": global_row_success,
                "packet_outcome": packet_outcome,
            },
            "summary": {
                "all_criteria_satisfied": scientific_state_change,
                "phase_status": "COMPLETE" if scientific_state_change else "INCOMPLETE",
                "next_action": (
                    "RECOMPUTE_BLOCKER_STATE_AND_DECIDE_CONTINUE_OR_ESCALATE"
                    if scientific_state_change
                    else "ESCALATE_TO_NEXT_ATTACK_CLASS"
                ),
            },
        },
        "summary": {
            "packet_outcome": packet_outcome,
            "usable_boundary_mapped": usable_boundary_mapped,
            "condition_b_regime_limiter_confirmed": condition_b_is_limiter,
            "boundary_sharpness": round(boundary_sharpness, 6),
            "scientific_state_change_observed": scientific_state_change,
            "blocker_facing_movement_observed": blocker_facing_movement,
            "next_action": (
                "RECOMPUTE_BLOCKER_STATE_AND_DECIDE_CONTINUE_OR_ESCALATE"
                if scientific_state_change
                else "ESCALATE_TO_NEXT_ATTACK_CLASS"
            ),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "cross_anchor_report": _ptr(cross_anchor_report_path),
            "trend": _ptr(TREND_PATH),
            "row_outcome_trend": _ptr(ROW_TREND_PATH),
        },
        "non_claim_boundary": "Repository-local simulation-first falsification packet report; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate simulation-first falsification packet v2 boundary report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument("--cross-anchor-report", type=Path, required=True)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "simulation_first_falsification_packet_report_20260411_v2.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    cross_anchor_report_path = ns.cross_anchor_report if ns.cross_anchor_report.is_absolute() else (REPO_ROOT / ns.cross_anchor_report)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(
        declaration_path=declaration_path,
        cross_anchor_report_path=cross_anchor_report_path,
        captured_at_utc=ns.captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "simulation_first_falsification_packet_v2_boundary_report: "
        f"packet_outcome={payload['summary']['packet_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
