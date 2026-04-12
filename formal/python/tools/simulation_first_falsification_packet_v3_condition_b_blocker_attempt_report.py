from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SIMULATION_FIRST_FALSIFICATION_PACKET_REPORT_20260411_v3"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SIMULATION_FIRST_FALSIFICATION_PACKET_20260411_v3.json"
)
DEFAULT_V2_PACKET_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "simulation_first_falsification_packet_report_20260411_v2.json"
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


def build_report(
    *,
    declaration_path: Path,
    v2_packet_report_path: Path,
    cross_anchor_report_path: Path,
    captured_at_utc: str | None,
) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    v2_packet = _read_json(v2_packet_report_path)
    trend = _read_json(TREND_PATH)
    row_trend = _read_json(ROW_TREND_PATH)
    cross_anchor_md = _read_text(cross_anchor_report_path)

    counts = _extract_counts(cross_anchor_md)
    a_pass = counts["condition_A"]["PASS"]
    a_fail = counts["condition_A"]["FAIL"]
    b_pass = counts["condition_B"]["PASS"]
    b_fail = counts["condition_B"]["FAIL"]

    a_total = a_pass + a_fail
    b_total = b_pass + b_fail

    pass_rate_a = _rate(a_pass, a_total)
    pass_rate_b = _rate(b_pass, b_total)
    fail_rate_a = _rate(a_fail, a_total)
    fail_rate_b = _rate(b_fail, b_total)
    boundary_sharpness = pass_rate_a - pass_rate_b

    regime_assumption = declaration.get("regime_assumption", {})
    min_sharpness = float(regime_assumption.get("minimum_boundary_sharpness_required", 0.5) or 0.5)
    limiter_required = bool(regime_assumption.get("condition_b_regime_limiter_confirmed_required", True))

    v2_summary = v2_packet.get("summary", {})
    v2_limiter_confirmed = bool(v2_summary.get("condition_b_regime_limiter_confirmed", False))
    v2_sharpness = float(v2_summary.get("boundary_sharpness", 0.0) or 0.0)

    current_limiter_confirmed = fail_rate_b > fail_rate_a
    regime_precondition_met = (
        (v2_limiter_confirmed if limiter_required else True)
        and v2_sharpness >= min_sharpness
        and current_limiter_confirmed
        and boundary_sharpness >= min_sharpness
    )

    prior_counts = trend.get("blocker_counts", {}).get("prior", {})
    current_counts = trend.get("blocker_counts", {}).get("current", {})

    blocker_target = declaration.get("blocker_target", {})
    named_blocker_class = str(blocker_target.get("named_blocker_class", "THEOREM_GAP"))

    named_prior = int(prior_counts.get(named_blocker_class, 0) or 0)
    named_current = int(current_counts.get(named_blocker_class, named_prior) or named_prior)
    named_blocker_delta = named_current - named_prior

    theorem_prior = int(prior_counts.get("THEOREM_GAP", 0) or 0)
    theorem_current = int(current_counts.get("THEOREM_GAP", theorem_prior) or theorem_prior)
    theorem_delta = theorem_current - theorem_prior

    row_counts = row_trend.get("objective_quality", {}).get("inputs", {}).get("row_outcome_counts", {})
    global_row_success = sum(int((v or {}).get("success", 0) or 0) for v in row_counts.values()) if isinstance(row_counts, dict) else 0

    row_target = str(blocker_target.get("row_target", "ROW-PILLAR-COSMO-001"))
    row_target_success = int(((row_counts or {}).get(row_target, {}) or {}).get("success", 0) or 0) if isinstance(row_counts, dict) else 0

    theorem_gap_improved = theorem_delta < 0
    row_success_observed = global_row_success > 0
    named_blocker_state_changed = named_blocker_delta != 0

    blocker_movement = theorem_gap_improved or row_success_observed or named_blocker_state_changed

    if not regime_precondition_met:
        packet_outcome = "INCONCLUSIVE_REGIME_PRECONDITION_NOT_MET"
        scientific_state_change = False
    elif blocker_movement:
        packet_outcome = "BLOCKER_MOVEMENT_OBSERVED_INSIDE_CONDITION_B_REGIME"
        scientific_state_change = True
    else:
        packet_outcome = "NO_BLOCKER_MOVEMENT_INSIDE_CONDITION_B_REGIME"
        scientific_state_change = False

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "campaign_id": declaration.get("campaign_id"),
        "packet_id": declaration.get("packet_id"),
        "criteria": {
            "v2_regime_artifact_present": v2_packet_report_path.exists(),
            "cross_anchor_report_exists": cross_anchor_report_path.exists(),
            "regime_precondition_met": regime_precondition_met,
            "blocker_facing_target_applied": True,
        },
        "objective_quality": {
            "criteria": {
                "scientific_state_change_observed": scientific_state_change,
                "blocker_facing_movement_observed": blocker_movement,
                "named_blocker_class_changed_state": named_blocker_state_changed,
                "target_row_success_observed": row_target_success > 0,
            },
            "inputs": {
                "packet_outcome": packet_outcome,
                "condition_A_pass": a_pass,
                "condition_A_fail": a_fail,
                "condition_B_pass": b_pass,
                "condition_B_fail": b_fail,
                "pass_rate_condition_A": round(pass_rate_a, 6),
                "pass_rate_condition_B": round(pass_rate_b, 6),
                "fail_rate_condition_A": round(fail_rate_a, 6),
                "fail_rate_condition_B": round(fail_rate_b, 6),
                "boundary_sharpness_current": round(boundary_sharpness, 6),
                "boundary_sharpness_minimum": min_sharpness,
                "v2_boundary_sharpness": round(v2_sharpness, 6),
                "v2_condition_b_limiter_confirmed": v2_limiter_confirmed,
                "current_condition_b_limiter_confirmed": current_limiter_confirmed,
                "named_blocker_class": named_blocker_class,
                "named_blocker_prior": named_prior,
                "named_blocker_current": named_current,
                "named_blocker_delta": named_blocker_delta,
                "theorem_gap_prior": theorem_prior,
                "theorem_gap_current": theorem_current,
                "theorem_gap_delta": theorem_delta,
                "global_row_success_count": global_row_success,
                "row_target": row_target,
                "row_target_success_count": row_target_success,
            },
            "summary": {
                "all_criteria_satisfied": blocker_movement,
                "phase_status": "COMPLETE" if regime_precondition_met else "INCOMPLETE",
                "next_action": (
                    "RECOMPUTE_BLOCKER_STATE_AND_CONFIRM_REDUCTION"
                    if blocker_movement
                    else "DECLARE_OPERATIONALLY_NONPRODUCTIVE_AND_ESCALATE"
                ),
            },
        },
        "summary": {
            "packet_outcome": packet_outcome,
            "regime_precondition_met": regime_precondition_met,
            "condition_b_regime_limiter_confirmed": current_limiter_confirmed,
            "boundary_sharpness": round(boundary_sharpness, 6),
            "scientific_state_change_observed": scientific_state_change,
            "blocker_facing_movement_observed": blocker_movement,
            "theorem_gap_delta": theorem_delta,
            "global_row_success_count": global_row_success,
            "named_blocker_class_changed_state": named_blocker_state_changed,
            "next_action": (
                "RECOMPUTE_BLOCKER_STATE_AND_CONFIRM_REDUCTION"
                if blocker_movement
                else "DECLARE_OPERATIONALLY_NONPRODUCTIVE_AND_ESCALATE"
            ),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "v2_packet_report": _ptr(v2_packet_report_path),
            "cross_anchor_report": _ptr(cross_anchor_report_path),
            "trend": _ptr(TREND_PATH),
            "row_outcome_trend": _ptr(ROW_TREND_PATH),
        },
        "non_claim_boundary": "Repository-local regime-conditioned blocker-attempt packet report; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate simulation-first falsification packet v3 condition_B blocker-attempt report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument("--v2-packet-report", type=Path, default=DEFAULT_V2_PACKET_REPORT_PATH)
    parser.add_argument("--cross-anchor-report", type=Path, required=True)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "simulation_first_falsification_packet_report_20260411_v3.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    v2_packet_report_path = ns.v2_packet_report if ns.v2_packet_report.is_absolute() else (REPO_ROOT / ns.v2_packet_report)
    cross_anchor_report_path = ns.cross_anchor_report if ns.cross_anchor_report.is_absolute() else (REPO_ROOT / ns.cross_anchor_report)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(
        declaration_path=declaration_path,
        v2_packet_report_path=v2_packet_report_path,
        cross_anchor_report_path=cross_anchor_report_path,
        captured_at_utc=ns.captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "simulation_first_falsification_packet_v3_condition_b_blocker_attempt_report: "
        f"packet_outcome={payload['summary']['packet_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
