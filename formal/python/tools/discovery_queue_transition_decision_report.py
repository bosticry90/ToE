from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.discovery_priority_queue_report import build_report as build_priority_queue_report
from formal.python.tools.qft_gr_discovery_post_cycle_decision_report import build_report as build_qft_post_cycle_report
from formal.python.tools.qm_stat_discovery_post_derivation_probe_decision_report import (
    build_report as build_qm_post_cycle_report,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "DISCOVERY_QUEUE_TRANSITION_DECISION_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "DISCOVERY_QUEUE_TRANSITION_DECISION_20260411_v0.json"
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


def _ensure_queue_report(path: Path, captured_at_utc: str | None) -> None:
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


def _ensure_qm_post_cycle(path: Path, captured_at_utc: str | None) -> None:
    if path.exists():
        return
    declaration = REPO_ROOT / "formal" / "docs" / "release" / "QM_STAT_DISCOVERY_POST_DERIVATION_PROBE_DECISION_20260411_v0.json"
    generated = build_qm_post_cycle_report(declaration_path=declaration, captured_at_utc=captured_at_utc)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(generated, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _ensure_qft_post_cycle(path: Path, captured_at_utc: str | None) -> None:
    if path.exists():
        return
    declaration = REPO_ROOT / "formal" / "docs" / "release" / "QFT_GR_DISCOVERY_POST_CYCLE_DECISION_20260411_v0.json"
    generated = build_qft_post_cycle_report(declaration_path=declaration, captured_at_utc=captured_at_utc)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(generated, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _as_int(value: Any) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        return int(value)
    return None


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    decision_policy = dict(declaration.get("decision_policy", {}))

    queue_report_path = REPO_ROOT / str(required_inputs.get("discovery_priority_queue_report", "")).strip()
    qm_post_cycle_path = REPO_ROOT / str(required_inputs.get("qm_stat_post_cycle_decision_report", "")).strip()
    qft_post_cycle_path = REPO_ROOT / str(required_inputs.get("qft_gr_post_cycle_decision_report", "")).strip()

    _ensure_queue_report(queue_report_path, captured_at_utc)
    _ensure_qm_post_cycle(qm_post_cycle_path, captured_at_utc)
    _ensure_qft_post_cycle(qft_post_cycle_path, captured_at_utc)

    queue_report = _read_json(queue_report_path)
    qm_post_cycle = _read_json(qm_post_cycle_path)
    qft_post_cycle = _read_json(qft_post_cycle_path)

    ranked_candidates = list(queue_report.get("ranked_candidates", []))
    internal_rows = {
        str(item).strip()
        for item in list(decision_policy.get("current_internal_discriminator_rows", []))
        if str(item).strip()
    }

    eligible = [
        row
        for row in ranked_candidates
        if str(row.get("row_id", "")).strip() and str(row.get("row_id", "")).strip() not in internal_rows
    ]

    candidate = eligible[0] if eligible else None
    runner_up = eligible[1] if len(eligible) > 1 else None

    candidate_score = _as_int(candidate.get("score")) if candidate is not None else None
    runner_up_score = _as_int(runner_up.get("score")) if runner_up is not None else None
    score_gap = (
        candidate_score - runner_up_score
        if candidate_score is not None and runner_up_score is not None
        else None
    )

    threshold = int(decision_policy.get("min_rank3_score_gap_over_rank4_for_activation", 3))
    gap_is_clear = score_gap is not None and score_gap >= threshold

    qm_decision = str(qm_post_cycle.get("summary", {}).get("post_cycle_decision", "")).strip()
    qft_decision = str(qft_post_cycle.get("summary", {}).get("post_cycle_decision", "")).strip()

    qm_internal_only = qm_decision == "KEEP_QM_STAT_AS_INTERNAL_DISCRIMINATOR_LANE"
    qft_internal_only = qft_decision == "KEEP_QFT_GR_AS_INTERNAL_DISCRIMINATOR_LANE"
    require_internal_only = bool(decision_policy.get("require_two_internal_only_seam_decisions", True))
    internal_only_ok = (qm_internal_only and qft_internal_only) if require_internal_only else True

    require_distinct_rank3 = bool(decision_policy.get("require_distinct_rank3_candidate", True))
    has_distinct_candidate = candidate is not None
    distinct_ok = has_distinct_candidate if require_distinct_rank3 else True

    activate = internal_only_ok and distinct_ok and gap_is_clear

    if activate:
        route_id = "ACTIVATE_NEXT_RANKED_SEAM_BOUNDED_SHADOW"
        route_name = "ACTIVATE_NEXT_RANKED_SEAM_BOUNDED_SHADOW"
        next_action = "ACTIVATE_NEXT_RANKED_SEAM_UNDER_SHADOW_SINGLE_CYCLE"
        reason = "RANK3_CLEARLY_SEPARATED_AND_TWO_INTERNAL_ONLY_SEAMS_CONFIRMED"
    else:
        route_id = "EXECUTE_BOUNDED_QUEUE_REVIEW_PASS"
        route_name = "EXECUTE_BOUNDED_QUEUE_REVIEW_PASS"
        next_action = "GENERATE_QUEUE_REVIEW_PASS_PACKET_AND_REVALIDATE_RANKING"
        reason = "DEFAULT_QUEUE_REVIEW_FOR_WEAK_OR_NOISY_RANKING_OR_UNSATISFIED_PRECONDITIONS"

    next_row_id = str(candidate.get("row_id", "")).strip() if candidate is not None else ""
    next_lane = str(candidate.get("lane", "")).strip() if candidate is not None else ""
    next_rank = _as_int(candidate.get("rank")) if candidate is not None else None

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "summary": {
            "selected_route": route_name,
            "selected_route_id": route_id,
            "selection_reason": reason,
            "next_action": next_action,
            "next_ranked_row_id": next_row_id,
            "next_ranked_lane": next_lane,
            "next_ranked_rank": next_rank,
            "next_ranked_score": candidate_score,
            "runner_up_ranked_score": runner_up_score,
            "rank3_over_rank4_score_gap": score_gap,
            "clear_gap_threshold": threshold,
            "external_discriminative_leverage_established": False,
            "qm_stat_internal_only_confirmed": qm_internal_only,
            "qft_gr_internal_only_confirmed": qft_internal_only,
            "activation_mode": str(decision_policy.get("activation_mode", "")).strip(),
            "max_new_seam_activations_per_cycle": int(
                decision_policy.get("max_new_seam_activations_per_cycle", 1)
            ),
        },
        "criteria": {
            "two_internal_only_precondition_satisfied": internal_only_ok,
            "distinct_rank3_candidate_available": distinct_ok,
            "rank3_score_gap_clearly_separated": gap_is_clear,
            "activation_selected": activate,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "discovery_priority_queue_report": _ptr(queue_report_path),
            "qm_stat_post_cycle_decision_report": _ptr(qm_post_cycle_path),
            "qft_gr_post_cycle_decision_report": _ptr(qft_post_cycle_path),
        },
        "non_claim_boundary": "Repository-local discovery queue transition decision report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate bounded discovery queue transition decision report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "discovery_queue_transition_decision_report_20260411_v0.json",
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
        "discovery_queue_transition_decision_report: "
        f"selected_route={payload['summary']['selected_route']} "
        f"next_ranked_row_id={payload['summary']['next_ranked_row_id']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())