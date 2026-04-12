from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SIMULATION_FIRST_FALSIFICATION_PACKET_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SIMULATION_FIRST_FALSIFICATION_PACKET_20260411_v0.json"
)
TREND_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json"
ROW_TREND_PATH = REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_row_outcome_trend_20260411_v0.json"


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


def _count_tol_checks(md_text: str) -> tuple[int, int]:
    pass_count = len(re.findall(r"\|\s*PASS\s*\|", md_text))
    fail_count = len(re.findall(r"\|\s*FAIL\s*\|", md_text))
    return pass_count, fail_count


def build_report(*, declaration_path: Path, cross_anchor_report_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    trend = _read_json(TREND_PATH)
    row_trend = _read_json(ROW_TREND_PATH)
    cross_anchor_md = _read_text(cross_anchor_report_path)

    pass_count, fail_count = _count_tol_checks(cross_anchor_md)
    total_checks = pass_count + fail_count

    theorem_prior = int(trend.get("blocker_counts", {}).get("prior", {}).get("THEOREM_GAP", 0))
    theorem_current = int(trend.get("blocker_counts", {}).get("current", {}).get("THEOREM_GAP", theorem_prior))
    theorem_delta = theorem_current - theorem_prior

    row_counts = row_trend.get("objective_quality", {}).get("inputs", {}).get("row_outcome_counts", {})
    global_row_success = sum(int((v or {}).get("success", 0) or 0) for v in row_counts.values()) if isinstance(row_counts, dict) else 0

    if total_checks == 0:
        packet_outcome = "INCONCLUSIVE"
        scientific_state_change = False
    elif fail_count > 0:
        packet_outcome = "FAILURE_ROUTE_FALSIFIED_OR_WEAKENED"
        scientific_state_change = True
    elif pass_count > 0:
        packet_outcome = "SUCCESS_ROUTE_VIABILITY_STRENGTHENED"
        scientific_state_change = True
    else:
        packet_outcome = "INCONCLUSIVE"
        scientific_state_change = False

    blocker_facing_movement = theorem_delta < 0 or global_row_success > 0

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "campaign_id": declaration.get("campaign_id"),
        "packet_id": declaration.get("packet_id"),
        "criteria": {
            "cross_anchor_report_exists": cross_anchor_report_path.exists(),
            "comparison_rows_present": total_checks > 0,
            "packet_outcome_decidable": packet_outcome != "INCONCLUSIVE" or total_checks == 0,
            "blocker_recompute_inputs_present": True,
        },
        "objective_quality": {
            "criteria": {
                "scientific_state_change_observed": scientific_state_change,
                "blocker_facing_movement_observed": blocker_facing_movement,
                "route_falsification_or_strengthening_evidence_observed": total_checks > 0,
            },
            "inputs": {
                "tol_check_pass_count": pass_count,
                "tol_check_fail_count": fail_count,
                "tol_check_total": total_checks,
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
                    "RECOMPUTE_BLOCKER_STATE_AND_UPDATE_STRATEGY"
                    if scientific_state_change
                    else "ESCALATE_TO_NEXT_ATTACK_CLASS"
                ),
            },
        },
        "summary": {
            "packet_outcome": packet_outcome,
            "scientific_state_change_observed": scientific_state_change,
            "blocker_facing_movement_observed": blocker_facing_movement,
            "next_action": (
                "RECOMPUTE_BLOCKER_STATE_AND_UPDATE_STRATEGY"
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
    parser = argparse.ArgumentParser(description="Generate simulation-first falsification packet report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument("--cross-anchor-report", type=Path, required=True)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "simulation_first_falsification_packet_report_20260411_v0.json",
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
        "simulation_first_falsification_packet_report: "
        f"packet_outcome={payload['summary']['packet_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
