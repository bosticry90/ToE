from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.discovery_priority_queue_report import build_report as build_priority_queue_report
from formal.python.tools.discovery_queue_review_pass_report import build_report as build_queue_review_report


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "DISCOVERY_QUEUE_RESCORING_PASS_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "DISCOVERY_QUEUE_RESCORING_PASS_20260411_v0.json"
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


def _as_int(value: Any) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        return int(value)
    return None


def _ensure_review(path: Path, captured_at_utc: str | None) -> None:
    if path.exists():
        return
    declaration = REPO_ROOT / "formal" / "docs" / "release" / "DISCOVERY_QUEUE_REVIEW_PASS_20260411_v0.json"
    generated = build_queue_review_report(declaration_path=declaration, captured_at_utc=captured_at_utc)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(generated, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _ensure_queue(path: Path, captured_at_utc: str | None) -> None:
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
    policy = dict(declaration.get("rescoring_policy", {}))
    factor_policy = dict(policy.get("bounded_factor_adjustments", {}))

    review_path = REPO_ROOT / str(required_inputs.get("discovery_queue_review_pass_report", "")).strip()
    queue_path = REPO_ROOT / str(required_inputs.get("discovery_priority_queue_report", "")).strip()

    _ensure_review(review_path, captured_at_utc)
    _ensure_queue(queue_path, captured_at_utc)

    review = _read_json(review_path)
    queue = _read_json(queue_path)

    review_summary = dict(review.get("summary", {}))
    review_route = str(review_summary.get("selected_next_route", "")).strip()
    weak_factors = list(review_summary.get("weak_or_noisy_scoring_factors", []))
    min_delta = dict(review_summary.get("minimum_activation_delta", {}))
    current_gap = _as_int(min_delta.get("current_rank3_over_rank4_gap"))
    threshold = int(policy.get("rank_gap_threshold", 3))

    ranked = list(queue.get("ranked_candidates", []))
    rank3 = next((row for row in ranked if _as_int(row.get("rank")) == 3), None)
    rank4 = next((row for row in ranked if _as_int(row.get("rank")) == 4), None)

    evidence_backing = {
        "RANK3_BLOCKER_LEVERAGE_PRESENT": rank3 is not None and _as_int(rank3.get("blocker_leverage")) is not None,
        "RANK3_EMPIRICAL_PROXIMITY_PRESENT": rank3 is not None and _as_int(rank3.get("empirical_proximity")) is not None,
        "RANK3_AND_RANK4_SCORES_PRESENT": rank3 is not None and rank4 is not None and _as_int(rank3.get("score")) is not None and _as_int(rank4.get("score")) is not None,
    }

    max_adjust = int(policy.get("max_total_gap_adjustment_points", 2))
    applied_adjustment = 0
    reweighted_or_clarified_factors: list[dict[str, Any]] = []

    for factor in weak_factors:
        conf = dict(factor_policy.get(str(factor), {}))
        if not conf:
            continue
        evidence_rule = str(conf.get("evidence_rule", "")).strip()
        supported = bool(evidence_backing.get(evidence_rule, False))
        requested = int(conf.get("gap_adjustment", 0))
        remaining = max_adjust - applied_adjustment
        granted = min(requested, remaining) if supported and remaining > 0 else 0
        applied_adjustment += granted
        reweighted_or_clarified_factors.append(
            {
                "factor": factor,
                "mode": str(conf.get("mode", "CLARIFY")),
                "evidence_rule": evidence_rule,
                "evidence_backed": supported,
                "requested_gap_adjustment": requested,
                "applied_gap_adjustment": granted,
            }
        )

    if current_gap is None:
        new_gap = None
    else:
        new_gap = current_gap + applied_adjustment

    route_precondition = review_route == str(policy.get("expected_review_route", "")).strip()
    activation_justified = new_gap is not None and new_gap >= threshold and route_precondition

    if activation_justified:
        selected_next_route = "ACTIVATE_NEXT_RANKED_SEAM"
        terminal_outcome = "ACTIVATE_NEXT_RANKED_SEAM"
    elif route_precondition and new_gap is not None:
        selected_next_route = "HOLD_QUEUE_AFTER_RESCORING"
        terminal_outcome = "HOLD_QUEUE_AFTER_RESCORING"
    else:
        selected_next_route = "QUEUE_RESCORING_INSUFFICIENT"
        terminal_outcome = "QUEUE_RESCORING_INSUFFICIENT"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "summary": {
            "review_outcome": "BOUNDED_QUEUE_RESCORING_EXECUTED",
            "rank3_candidate": str(min_delta.get("candidate_rank3", "")).strip(),
            "rank_gap_before_rescoring": current_gap,
            "rank_gap_after_rescoring": new_gap,
            "rank_gap_threshold": threshold,
            "rank_separation_status_after_rescoring": "CLEAR" if (new_gap is not None and new_gap >= threshold) else "WEAK_OR_NOISY",
            "reweighted_or_clarified_factors": reweighted_or_clarified_factors,
            "evidence_backed_and_bounded": bool(route_precondition),
            "minimum_activation_delta": {
                "required_rank3_over_rank4_gap": threshold,
                "current_rank3_over_rank4_gap": current_gap,
                "applied_gap_adjustment": applied_adjustment,
                "remaining_gap_needed": (threshold - new_gap) if new_gap is not None and new_gap < threshold else 0,
            },
            "activation_now_justified": activation_justified,
            "selected_next_route": selected_next_route,
            "terminal_route": terminal_outcome,
            "no_loop_rule": str(policy.get("no_loop_rule", "")).strip(),
        },
        "criteria": {
            "review_selected_one_bounded_rescoring": route_precondition,
            "bounded_adjustment_cap_respected": applied_adjustment <= max_adjust,
            "new_rank_gap_computed": new_gap is not None,
            "terminal_route_materialized": terminal_outcome in {
                "ACTIVATE_NEXT_RANKED_SEAM",
                "HOLD_QUEUE_AFTER_RESCORING",
                "QUEUE_RESCORING_INSUFFICIENT",
            },
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "discovery_queue_review_pass_report": _ptr(review_path),
            "discovery_priority_queue_report": _ptr(queue_path),
        },
        "non_claim_boundary": "Repository-local bounded queue rescoring pass report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate bounded discovery queue rescoring pass report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "discovery_queue_rescoring_pass_report_20260411_v0.json",
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
        "discovery_queue_rescoring_pass_report: "
        f"terminal_route={payload['summary']['terminal_route']} "
        f"rank_gap_after_rescoring={payload['summary']['rank_gap_after_rescoring']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())