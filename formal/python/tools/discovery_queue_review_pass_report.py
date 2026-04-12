from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.discovery_priority_queue_report import build_report as build_priority_queue_report
from formal.python.tools.discovery_queue_transition_decision_report import (
    build_report as build_transition_report,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "DISCOVERY_QUEUE_REVIEW_PASS_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "DISCOVERY_QUEUE_REVIEW_PASS_20260411_v0.json"
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


def _ensure_transition(path: Path, captured_at_utc: str | None) -> None:
    if path.exists():
        return
    declaration = REPO_ROOT / "formal" / "docs" / "release" / "DISCOVERY_QUEUE_TRANSITION_DECISION_20260411_v0.json"
    generated = build_transition_report(declaration_path=declaration, captured_at_utc=captured_at_utc)
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
    policy = dict(declaration.get("decision_policy", {}))

    transition_path = REPO_ROOT / str(required_inputs.get("discovery_queue_transition_decision_report", "")).strip()
    queue_path = REPO_ROOT / str(required_inputs.get("discovery_priority_queue_report", "")).strip()

    _ensure_transition(transition_path, captured_at_utc)
    _ensure_queue(queue_path, captured_at_utc)

    transition = _read_json(transition_path)
    queue = _read_json(queue_path)

    summary = dict(transition.get("summary", {}))
    transition_route = str(summary.get("selected_route", "")).strip()
    rank3_row_id = str(summary.get("next_ranked_row_id", "")).strip()
    rank3_score = _as_int(summary.get("next_ranked_score"))
    rank4_score = _as_int(summary.get("runner_up_ranked_score"))
    score_gap = _as_int(summary.get("rank3_over_rank4_score_gap"))
    threshold = int(policy.get("rank3_gap_threshold", 3))
    gap_clear = score_gap is not None and score_gap >= threshold

    ranked = list(queue.get("ranked_candidates", []))
    rank3_entry = next((r for r in ranked if _as_int(r.get("rank")) == 3), None)
    rank4_entry = next((r for r in ranked if _as_int(r.get("rank")) == 4), None)

    if score_gap is None:
        weak_reason = "INSUFFICIENT_ELIGIBLE_CANDIDATES"
    elif score_gap < threshold:
        weak_reason = "RANK3_GAP_BELOW_THRESHOLD"
    else:
        weak_reason = "RANK3_GAP_BELOW_THRESHOLD"

    weak_or_noisy_scoring_factors: list[str] = []
    if rank3_entry is not None:
        if _as_int(rank3_entry.get("blocker_leverage")) is not None and _as_int(rank3_entry.get("blocker_leverage")) <= 4:
            weak_or_noisy_scoring_factors.append("BLOCKER_LEVERAGE_NOT_DOMINANT")
        if _as_int(rank3_entry.get("empirical_proximity")) is not None and _as_int(rank3_entry.get("empirical_proximity")) <= 3:
            weak_or_noisy_scoring_factors.append("EMPIRICAL_PROXIMITY_MODERATE")
    if rank4_entry is not None and rank3_score is not None and rank4_score is not None and (rank3_score - rank4_score) <= 1:
        weak_or_noisy_scoring_factors.append("RANK3_RANK4_NEAR_TIE")
    if not weak_or_noisy_scoring_factors:
        weak_or_noisy_scoring_factors.append("MIXED_OR_NOISY_DIMENSIONS")

    minimum_activation_delta = {
        "required_rank3_over_rank4_gap": threshold,
        "current_rank3_over_rank4_gap": score_gap,
        "additional_gap_needed": (threshold - score_gap) if score_gap is not None and score_gap < threshold else 0,
        "candidate_rank3": rank3_row_id,
    }

    supports_queue_review = transition_route == str(policy.get("expected_transition_route", "")).strip()
    allow_rescore_once = bool(policy.get("allow_one_bounded_queue_rescoring", True))

    if gap_clear:
        review_outcome = "QUEUE_REVIEW_SUPPORTS_NEXT_SEAM_ACTIVATION"
        selected_next_route = "ACTIVATE_NEXT_RANKED_SEAM_BOUNDED_SHADOW"
    elif supports_queue_review and allow_rescore_once:
        review_outcome = "QUEUE_REVIEW_SUPPORTS_ONE_BOUNDED_QUEUE_RESCORING"
        selected_next_route = "EXECUTE_ONE_BOUNDED_QUEUE_RESCORING"
    elif supports_queue_review:
        review_outcome = "QUEUE_REVIEW_SUPPORTS_HOLD"
        selected_next_route = "EXECUTE_BOUNDED_QUEUE_REVIEW_PASS"
    else:
        review_outcome = "QUEUE_REVIEW_INSUFFICIENT_EVIDENCE"
        selected_next_route = "EXECUTE_BOUNDED_QUEUE_REVIEW_PASS"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "summary": {
            "review_outcome": review_outcome,
            "rank3_candidate": rank3_row_id,
            "rank_separation_status": "CLEAR" if gap_clear else "WEAK_OR_NOISY",
            "weak_or_noisy_scoring_factors": weak_or_noisy_scoring_factors,
            "minimum_activation_delta": minimum_activation_delta,
            "selected_next_route": selected_next_route,
            "no_loop_rule": str(policy.get("no_loop_rule", "")).strip(),
        },
        "criteria": {
            "transition_route_matches_expected_queue_review": supports_queue_review,
            "rank3_candidate_present": bool(rank3_row_id),
            "rank_gap_meets_threshold": gap_clear,
            "bounded_review_materialized": True,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "discovery_queue_transition_decision_report": _ptr(transition_path),
            "discovery_priority_queue_report": _ptr(queue_path),
        },
        "non_claim_boundary": "Repository-local bounded discovery queue review pass report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate bounded discovery queue review pass report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "discovery_queue_review_pass_report_20260411_v0.json",
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
        "discovery_queue_review_pass_report: "
        f"review_outcome={payload['summary']['review_outcome']} "
        f"selected_next_route={payload['summary']['selected_next_route']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())