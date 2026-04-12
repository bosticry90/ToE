from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PACKET41_REVIEW_LAYER_CLEARANCE_DECOMPOSITION_20260411_v0"

CYCLE02_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "toe_qft_gr_seam_packet41_reconsideration_scorecard_evaluation_cycle02_checkpoint_v0.json"
)
REWORK_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "packet41_numeric_clearance_rework_tranche_20260411_v0.json"
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
    rework = _read_json(REWORK_PATH)

    review = cycle02.get("payload", {}).get("review_layer_pass", {})
    components = {
        "packet41_eligibility_review_pass": bool(review.get("packet41_eligibility_review_pass", False)),
        "packet41_targeted_justification_review_pass": bool(review.get("packet41_targeted_justification_review_pass", False)),
        "packet41_hold_fork_release_condition_pass": bool(review.get("packet41_hold_fork_release_condition_pass", False)),
        "retrospective_cumulative_delta_audit_release_condition_pass": bool(
            review.get("retrospective_cumulative_delta_audit_release_condition_pass", False)
        ),
    }

    required = list(components.keys())
    passed = [name for name, ok in components.items() if ok]
    missing = [name for name, ok in components.items() if not ok]

    pass_count = len(passed)
    target = len(required)
    gap = target - pass_count

    success_ladder = {
        "minimum_success": {
            "rule": "review_layer_pass_count_gt_0",
            "satisfied": pass_count > 0,
        },
        "stronger_success": {
            "rule": "review_layer_pass_count_gte_2",
            "satisfied": pass_count >= 2,
        },
        "full_success": {
            "rule": "review_layer_pass_count_eq_4_and_threshold4_clears",
            "satisfied": pass_count == 4,
        },
    }

    criteria = {
        "all_four_review_layer_components_identified": len(required) == 4,
        "missing_component_set_materialized": len(missing) >= 0,
        "single_actionable_parameter_preserved": rework.get("actionable_parameter", {}).get("name") == "review_layer_pass_count",
        "packet41_only_focus_ready": True,
    }

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "target": "PACKET41_REVIEW_LAYER_PASS_COUNT_LIFT",
        "decomposition": {
            "required_components": required,
            "component_status": components,
            "missing_components": missing,
            "passed_components": passed,
            "pass_count": pass_count,
            "target_count": target,
            "gap": gap,
            "dependency_model": "CONJUNCTIVE_ALL_REQUIRED",
            "sequential_dependency_required": False,
        },
        "success_ladder": success_ladder,
        "criteria": criteria,
        "summary": {
            "outcome": "PASS_COUNT_LIFTED" if pass_count > 0 else "NO_LIFT",
            "next_action": "EXECUTE_PACKET41_ONLY_PASS_COUNT_LIFT_TRANCHE",
        },
        "source_bundle": {
            "cycle02_scorecard": _ptr(CYCLE02_PATH),
            "packet41_numeric_rework": _ptr(REWORK_PATH),
        },
        "non_claim_boundary": "Repository-local Packet41 review-layer decomposition artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate Packet41 review-layer clearance decomposition report.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "packet41_review_layer_clearance_decomposition_20260411_v0.json",
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
        "packet41_review_layer_clearance_decomposition_report: "
        f"pass_count={payload['decomposition']['pass_count']} "
        f"target={payload['decomposition']['target_count']} "
        f"out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())