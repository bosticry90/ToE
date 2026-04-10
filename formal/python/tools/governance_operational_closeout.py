from __future__ import annotations

import argparse
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GOVERNANCE_OPERATIONAL_REFINEMENT_CLOSEOUT_20260410_v0"

AUDIT_PACKET_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_audit_packet_20260410_v0.json"
CHECKPOINT_SUMMARY_PATH = REPO_ROOT / "formal" / "output" / "reports" / "checkpoint_ladder_acceptance_summary_v0.json"


REQUIRED_PACKET_SECTIONS = [
    "runtime_baselines",
    "artifact_growth_tracking",
    "artifact_lifecycle_policy",
    "closure_map",
    "promotion_readiness",
    "promotion_action_policy",
    "freshness_validation",
    "blocker_trend_window",
]


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _resolve_timestamp(captured_at_utc: str | None) -> str:
    if captured_at_utc:
        return captured_at_utc
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _git_clean() -> bool:
    proc = subprocess.run(
        ["git", "status", "--porcelain"],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        return False
    return proc.stdout.strip() == ""


def _git_synced_with_origin_main() -> bool:
    proc = subprocess.run(
        ["git", "rev-list", "--left-right", "--count", "origin/main...HEAD"],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        return False
    parts = proc.stdout.strip().split()
    if len(parts) != 2:
        return False
    behind, ahead = parts
    return behind == "0" and ahead == "0"


def _checkpoint_all_green(payload: dict[str, Any]) -> bool:
    steps = payload.get("step_results", [])
    if not isinstance(steps, list) or not steps:
        return False
    for step in steps:
        if not isinstance(step, dict):
            return False
        if step.get("status") != "PASSED":
            return False
    return bool(payload.get("failed") is False)


def build_closeout_report(*, output_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    packet = _read_json(AUDIT_PACKET_PATH)
    checkpoint = _read_json(CHECKPOINT_SUMMARY_PATH)

    packet_sections_present = all(section in packet for section in REQUIRED_PACKET_SECTIONS)
    action_policy_present = "promotion_action_policy" in packet
    freshness_enforced = "freshness_validation" in packet
    trend_enforced = "blocker_trend_window" in packet
    governance_and_ladder_green = _checkpoint_all_green(checkpoint)
    clean_tree_now = _git_clean()
    synced_main_now = _git_synced_with_origin_main()

    criteria = {
        "required_packet_sections_present": packet_sections_present,
        "readiness_action_policy_present": action_policy_present,
        "freshness_enforcement_present": freshness_enforced,
        "blocker_trend_enforcement_present": trend_enforced,
        "governance_and_checkpoint_green": governance_and_ladder_green,
        "clean_tree_now": clean_tree_now,
        "synced_with_origin_main_now": synced_main_now,
    }

    all_criteria_satisfied = all(criteria.values())

    payload = {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _resolve_timestamp(captured_at_utc),
        "closeout_rule": {
            "rule_id": "AUDIT_PACKET_OPERATIONAL_REFINEMENT_CLOSEOUT_v0",
            "description": "Operational refinement is complete only when all required packet controls exist and authoritative acceptance plus clean synced anchor criteria are satisfied.",
            "required_packet_sections": REQUIRED_PACKET_SECTIONS,
        },
        "criteria": criteria,
        "summary": {
            "all_criteria_satisfied": all_criteria_satisfied,
            "closeout_status": "COMPLETE" if all_criteria_satisfied else "INCOMPLETE",
            "next_action": "MAINTENANCE_MODE" if all_criteria_satisfied else "CONTINUE_REFINEMENT_OR_FINALIZE_ANCHOR",
        },
        "source_bundle": {
            "governance_audit_packet": str(AUDIT_PACKET_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "checkpoint_ladder_summary": str(CHECKPOINT_SUMMARY_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
        },
        "non_claim_boundary": "This closeout report is a repository-local governance control artifact and does not assert scientific adequacy.",
    }

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate operational refinement closeout report for audit packet governance controls.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "governance_operational_refinement_closeout_20260410_v0.json",
        help="Output path for closeout report JSON.",
    )
    parser.add_argument(
        "--captured-at-utc",
        default=None,
        help="Optional RFC3339 UTC timestamp override (e.g. 2026-04-10T00:00:00Z).",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    output_path = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_closeout_report(output_path=output_path, captured_at_utc=ns.captured_at_utc)
    print(
        "governance_operational_closeout: "
        f"status={payload['summary']['closeout_status']} "
        f"all_criteria={payload['summary']['all_criteria_satisfied']} "
        f"out={output_path}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
