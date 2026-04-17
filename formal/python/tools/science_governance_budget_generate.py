from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_GOVERNANCE_BUDGET_20260416_v0"

DASHBOARD_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json"
SCIENTIFIC_CORE_INDEX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "SCIENTIFIC_CORE_INDEX_v0.md"
PHYSICS_FIRST_RULE_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PHYSICS_FIRST_EXECUTION_RULE_v0.md"
THROUGHPUT_PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PHYS_MATH_THROUGHPUT_REMEDIATION_PROGRAM_v0.md"

PHASE_TARGET_BANDS = (
    {"phase": "PHASE2_LANE_SPLIT", "minimum_science_to_control_ratio": 1.0},
    {"phase": "PHASE3_THEOREM_DEPTH", "minimum_science_to_control_ratio": 1.5},
    {"phase": "PHASE4_SEAM_THROUGHPUT", "minimum_science_to_control_ratio": 1.25},
    {"phase": "PHASE5_SSOT_MIGRATION", "minimum_science_to_control_ratio": 1.0},
    {"phase": "PHASE6_LIVE_AUTHORIZATION", "minimum_science_to_control_ratio": 1.5},
)


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read_text(path))


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _resolve_timestamp(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _count_index_rows(index_text: str) -> tuple[int, int]:
    science_rows = 0
    control_rows = 0
    for line in index_text.splitlines():
        stripped = line.strip()
        if stripped.startswith("| `SCI-"):
            science_rows += 1
        elif stripped.startswith("| `CTL-"):
            control_rows += 1
    if science_rows == 0:
        raise ValueError("Scientific core index produced zero science rows.")
    if control_rows == 0:
        raise ValueError("Scientific core index produced zero governance-control rows.")
    return science_rows, control_rows


def _ratio(science_rows: int, control_rows: int) -> float:
    return round(science_rows / control_rows, 2)


def _phase_target_assessment(ratio: float) -> list[dict[str, Any]]:
    return [
        {
            "phase": band["phase"],
            "minimum_science_to_control_ratio": band["minimum_science_to_control_ratio"],
            "meets_target": ratio >= band["minimum_science_to_control_ratio"],
        }
        for band in PHASE_TARGET_BANDS
    ]


def _parse_bullet_section(text: str, header: str) -> list[str]:
    lines = text.splitlines()
    collected: list[str] = []
    in_section = False
    for line in lines:
        if line.strip() == header:
            in_section = True
            continue
        if in_section and line.startswith("## "):
            break
        if in_section and line.strip().startswith("- `"):
            collected.append(line.strip().strip("- ").strip("`"))
    return collected


def _budget_posture(*, ratio: float, dashboard: dict[str, Any]) -> dict[str, str]:
    movement_status = str(dashboard.get("blocker_scoreboard", {}).get("movement_status", "UNKNOWN"))
    exception_required = bool(dashboard.get("blocker_scoreboard", {}).get("exception_required", False))
    stale_inputs = bool(dashboard.get("source_freshness", {}).get("stale_input_warning", False))

    if movement_status != "DECREASING" and ratio < 1.25:
        posture = "CONTROL_HEAVY_REBALANCE_REQUIRED"
        reason = "BLOCKERS_ARE_NOT_SHRINKING_AND_REPRESENTATIVE_SCIENCE_SHARE_IS_TOO_LOW"
    elif movement_status != "DECREASING" and exception_required:
        posture = "SCIENCE_REBALANCE_REVIEW_REQUIRED"
        reason = "BLOCKERS_ARE_FLAT_OR_RISING_SO_NEW_WORK_SHOULD_FAVOR_BLOCKER_REDUCING_SCIENCE_SURFACES"
    elif stale_inputs:
        posture = "INPUT_REFRESH_REQUIRED_BEFORE_STRONGER_ENFORCEMENT"
        reason = "BUDGET_SIGNALS_EXIST_BUT_UPSTREAM_INPUTS_ARE_NOT_FULLY_FRESH"
    else:
        posture = "WITHIN_REPRESENTATIVE_BALANCE_BAND"
        reason = "REPRESENTATIVE_SURFACE_BALANCE_AND_BLOCKER_SIGNALS_DO_NOT_REQUIRE_IMMEDIATE_REBALANCE"

    recommendation = "KEEP_ACTIVE_WORK_SCIENCE_FIRST_AND_LIMIT_GOVERNANCE_WORK_TO_DIRECT_UNBLOCKERS"
    return {
        "budget_posture": posture,
        "reason": reason,
        "recommended_lane_allocation": recommendation,
    }


def build_budget_report(*, output_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    dashboard = _read_json(DASHBOARD_REPORT_PATH)
    index_text = _read_text(SCIENTIFIC_CORE_INDEX_PATH)
    physics_first_text = _read_text(PHYSICS_FIRST_RULE_PATH)
    throughput_text = _read_text(THROUGHPUT_PROGRAM_PATH)

    science_rows, control_rows = _count_index_rows(index_text)
    ratio = _ratio(science_rows, control_rows)
    phase_assessment = _phase_target_assessment(ratio)
    posture = _budget_posture(ratio=ratio, dashboard=dashboard)

    payload = {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _resolve_timestamp(captured_at_utc),
        "representative_surface_counts": {
            "science_core_rows": science_rows,
            "governance_control_rows": control_rows,
            "science_to_control_ratio": ratio,
        },
        "phase_target_assessment": {
            "bands": list(PHASE_TARGET_BANDS),
            "assessment": phase_assessment,
        },
        "dashboard_coupling": {
            "dashboard_pointer": _ptr(DASHBOARD_REPORT_PATH),
            "movement_status": str(dashboard.get("blocker_scoreboard", {}).get("movement_status", "")),
            "net_delta": int(dashboard.get("blocker_scoreboard", {}).get("net_delta", 0) or 0),
            "exception_required": bool(dashboard.get("blocker_scoreboard", {}).get("exception_required", False)),
            "stale_input_warning": bool(dashboard.get("source_freshness", {}).get("stale_input_warning", False)),
        },
        "execution_boundary": {
            "allowed_scientific_delta_classes": _parse_bullet_section(physics_first_text, "## Core Rule"),
            "allowed_support_only_categories": _parse_bullet_section(physics_first_text, "## Support Work Classification"),
            "throughput_program_pointer": _ptr(THROUGHPUT_PROGRAM_PATH),
            "throughput_phase_tokens_sample": [
                line.strip().lstrip("- ")
                for line in throughput_text.splitlines()
                if line.strip().startswith("- `PHYS_MATH_THROUGHPUT_PROGRAM_STATUS_v0:")
            ][:5],
        },
        "budget_posture": posture,
        "source_bundle": {
            "blocker_burn_dashboard": _ptr(DASHBOARD_REPORT_PATH),
            "scientific_core_index": _ptr(SCIENTIFIC_CORE_INDEX_PATH),
            "physics_first_execution_rule": _ptr(PHYSICS_FIRST_RULE_PATH),
            "throughput_program": _ptr(THROUGHPUT_PROGRAM_PATH),
        },
        "non_claim_boundary": "This budget report is a repository-local planning artifact and does not authorize scientific scope expansion by itself.",
    }

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate science-versus-governance budget report.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "science_governance_budget_20260416_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_budget_report(output_path=out, captured_at_utc=ns.captured_at_utc)
    print(
        "science_governance_budget_generate: "
        f"ratio={payload['representative_surface_counts']['science_to_control_ratio']} "
        f"posture={payload['budget_posture']['budget_posture']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())