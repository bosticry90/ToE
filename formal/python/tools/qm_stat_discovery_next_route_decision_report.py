from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.discovery_priority_queue_report import build_report as build_priority_queue_report
from formal.python.tools.qm_stat_discovery_post_derivation_probe_decision_report import (
    build_report as build_post_cycle_decision_report,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_DISCOVERY_NEXT_ROUTE_DECISION_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "QM_STAT_DISCOVERY_NEXT_ROUTE_DECISION_20260411_v0.json"
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


def _ensure_post_cycle_decision(path: Path, captured_at_utc: str | None) -> None:
    if path.exists():
        return
    declaration = REPO_ROOT / "formal" / "docs" / "release" / "QM_STAT_DISCOVERY_POST_DERIVATION_PROBE_DECISION_20260411_v0.json"
    generated = build_post_cycle_decision_report(declaration_path=declaration, captured_at_utc=captured_at_utc)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(generated, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _ensure_priority_queue(path: Path, captured_at_utc: str | None) -> None:
    if path.exists():
        return
    declaration = REPO_ROOT / "formal" / "docs" / "release" / "DISCOVERY_PRIORITY_QUEUE_20260411_v0.json"
    trend = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json"
    closure_map = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_closure_map_20260410_v0.json"
    ledger = REPO_ROOT / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json"
    generated = build_priority_queue_report(
        declaration_path=declaration,
        trend_path=trend,
        closure_map_path=closure_map,
        ledger_path=ledger,
        captured_at_utc=captured_at_utc,
    )
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(generated, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    decision_policy = dict(declaration.get("decision_policy", {}))

    post_cycle_path = REPO_ROOT / str(required_inputs.get("post_derivation_probe_decision_report", "")).strip()
    queue_path = REPO_ROOT / str(required_inputs.get("discovery_priority_queue_report", "")).strip()

    _ensure_post_cycle_decision(post_cycle_path, captured_at_utc)
    _ensure_priority_queue(queue_path, captured_at_utc)

    post_cycle = _read_json(post_cycle_path)
    queue = _read_json(queue_path)

    post_summary = dict(post_cycle.get("summary", {}))
    queue_rows = list(queue.get("ranked_candidates", []))

    post_cycle_decision = str(post_summary.get("post_cycle_decision", "")).strip()
    current_seam = dict(declaration.get("current_seam", {}))
    current_row_id = str(current_seam.get("row_id", "")).strip()

    selected_row = None
    selected_reason = ""
    for row in queue_rows:
        row_id = str(row.get("row_id", "")).strip()
        if row_id and row_id != current_row_id:
            selected_row = row
            selected_reason = "FIRST_NON_CURRENT_SEAM_FROM_PRIORITY_QUEUE"
            break

    stronger_comparator_packet = ""
    if post_cycle_decision == "REFINE_PROBE_COMPARATOR_ONCE_BOUNDED":
        stronger_comparator_packet = "MATERIALIZE_ONE_STRONGER_COMPARATOR_PACKET"

    if post_cycle_decision == "REFINE_PROBE_COMPARATOR_ONCE_BOUNDED":
        route = "REFINE_COMPARATOR_ONCE"
        route_name = "REFINE_PROBE_COMPARATOR_ONCE_BOUNDED"
        next_action = "MATERIALIZE_ONE_STRONGER_COMPARATOR_PACKET"
    else:
        route = "ACTIVATE_NEXT_RANKED_SEAM"
        route_name = "ACTIVATE_NEXT_RANKED_SEAM"
        if selected_row is None:
            next_action = "ADVANCE_DISCOVERY_QUEUE_REQUIRES_REFRESH_NO_ELIGIBLE_NEXT_SEAM"
            selected_reason = "NO_NON_CURRENT_SEAM_AVAILABLE_IN_QUEUE"
        else:
            next_action = "ADVANCE_DISCOVERY_QUEUE_TO_NEXT_SEAM"

    selected_row_id = ""
    selected_lane = ""
    selected_rank = None
    selected_score = None
    if selected_row is not None:
        selected_row_id = str(selected_row.get("row_id", "")).strip()
        selected_lane = str(selected_row.get("lane", "")).strip()
        rank_value = selected_row.get("rank")
        score_value = selected_row.get("score")
        selected_rank = int(rank_value) if isinstance(rank_value, int | float) else None
        selected_score = int(score_value) if isinstance(score_value, int | float) else None

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "summary": {
            "selected_route": route_name,
            "selected_route_id": route,
            "post_cycle_decision": post_cycle_decision,
            "current_seam_row_id": current_row_id,
            "next_ranked_row_id": selected_row_id,
            "next_ranked_lane": selected_lane,
            "next_ranked_rank": selected_rank,
            "next_ranked_score": selected_score,
            "selection_reason": selected_reason,
            "next_action": next_action,
            "auto_same_shape_qm_stat_rerun_allowed": False,
            "stronger_comparator_packet": stronger_comparator_packet or None,
        },
        "criteria": {
            "bounded_two_route_policy": bool(decision_policy.get("allow_only_two_routes", False)),
            "single_comparator_refinement_cap": int(decision_policy.get("max_comparator_refinement_cycles", 0)) == 1,
            "no_same_shape_autorerun_enforced": bool(decision_policy.get("no_same_shape_qm_stat_autorerun", False)),
            "default_preference_respected_when_no_refinement": (
                route == "ACTIVATE_NEXT_RANKED_SEAM"
                if post_cycle_decision != "REFINE_PROBE_COMPARATOR_ONCE_BOUNDED"
                else True
            ),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_derivation_probe_decision_report": _ptr(post_cycle_path),
            "discovery_priority_queue_report": _ptr(queue_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT next-route decision report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate QM-STAT next-route decision report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_discovery_next_route_decision_report_20260411_v0.json",
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
        "qm_stat_discovery_next_route_decision_report: "
        f"selected_route={payload['summary']['selected_route']} "
        f"next_ranked_row_id={payload['summary']['next_ranked_row_id']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())