from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GOVERNANCE_BLOCKER_TREND_WINDOW_20260410_v0"

BLOCKER_BURN_REVIEW_PATH = REPO_ROOT / "formal" / "output" / "ws10_tgc76_row_promotion_blocker_burn_review_checkpoint_20260408_v0.json"
BLOCKER_CLOSURE_MAP_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_closure_map_20260410_v0.json"


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _resolve_timestamp(captured_at_utc: str | None) -> str:
    if captured_at_utc:
        return captured_at_utc
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _movement_status(net_delta: int) -> str:
    if net_delta < 0:
        return "DECREASING"
    if net_delta == 0:
        return "FLAT"
    return "INCREASING"


def build_blocker_trend_window(*, output_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    blocker_review = _read_json(BLOCKER_BURN_REVIEW_PATH)
    blocker_map = _read_json(BLOCKER_CLOSURE_MAP_REPORT_PATH)

    blocker_counts = blocker_review.get("blocker_counts", {})
    if not isinstance(blocker_counts, dict):
        blocker_counts = {}
    prior = blocker_counts.get("prior", {})
    current = blocker_counts.get("current", {})
    if not isinstance(prior, dict):
        prior = {}
    if not isinstance(current, dict):
        current = {}

    net_delta_raw = blocker_counts.get("net_delta", 0)
    net_delta = int(net_delta_raw) if isinstance(net_delta_raw, int) else 0
    movement_status = _movement_status(net_delta)

    ccg02_exception = blocker_review.get("ccg02_exception", {})
    if not isinstance(ccg02_exception, dict):
        ccg02_exception = {}

    exception_required = bool(net_delta >= 0)
    exception_pointer = str(BLOCKER_BURN_REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/") if exception_required else None

    payload = {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _resolve_timestamp(captured_at_utc),
        "window": blocker_review.get("window", {}),
        "tranche_id": blocker_review.get("tranche_id"),
        "blocker_counts": {
            "prior": prior,
            "current": current,
            "net_delta": net_delta,
        },
        "trend_summary": {
            "movement_status": movement_status,
            "movement_rule": "NET_DELTA_LT_0_IS_PROGRESS_NET_DELTA_GE_0_REQUIRES_EXCEPTION",
            "row_coverage_count": int(blocker_map.get("rows_total", 0)),
        },
        "exception_requirement": {
            "exception_required": exception_required,
            "exception_artifact_pointer": exception_pointer,
            "ccg02_exception": ccg02_exception,
        },
        "source_bundle": {
            "blocker_burn_review": str(BLOCKER_BURN_REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "blocker_closure_map_report": str(BLOCKER_CLOSURE_MAP_REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
        },
        "non_claim_boundary": "This blocker trend window is a repository-local governance control artifact and does not assert scientific adequacy.",
    }

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate blocker trend window report for movement-or-exception enforcement.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json",
        help="Output path for blocker trend window report JSON.",
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

    payload = build_blocker_trend_window(output_path=output_path, captured_at_utc=ns.captured_at_utc)
    print(
        "governance_blocker_trend_window: "
        f"movement={payload['trend_summary']['movement_status']} "
        f"exception_required={payload['exception_requirement']['exception_required']} "
        f"out={output_path}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
