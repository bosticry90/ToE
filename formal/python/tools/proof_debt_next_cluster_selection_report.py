from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PROOF_DEBT_NEXT_CLUSTER_SELECTION_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "PROOF_DEBT_NEXT_CLUSTER_SELECTION_20260411_v0.json"
)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_optional_json(path: Path | None) -> dict[str, Any] | None:
    if path is None or not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _signal_score(signals: dict[str, Any], weights: dict[str, Any]) -> tuple[int, list[str]]:
    score = 0
    active: list[str] = []
    for key, weight in weights.items():
        enabled = bool(signals.get(key, False))
        if enabled:
            active.append(key)
            score += int(weight)
    return score, active


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)

    required_inputs = declaration.get("required_inputs", {})
    branch_ruling_path = REPO_ROOT / str(required_inputs.get("branch_ruling_report", ""))
    trend_path = REPO_ROOT / str(required_inputs.get("trend_pointer", ""))
    ledger_path = REPO_ROOT / str(required_inputs.get("ledger_pointer", ""))
    active_cluster_focus_relpath = str(required_inputs.get("active_cluster_focus_report", "")).strip()
    active_cluster_focus_path = None if not active_cluster_focus_relpath else (REPO_ROOT / active_cluster_focus_relpath)
    raw_cluster_focus_reports = required_inputs.get("cluster_focus_reports", [])
    if isinstance(raw_cluster_focus_reports, str):
        cluster_focus_report_relpaths = [raw_cluster_focus_reports]
    elif isinstance(raw_cluster_focus_reports, list):
        cluster_focus_report_relpaths = [str(item) for item in raw_cluster_focus_reports if str(item).strip()]
    else:
        cluster_focus_report_relpaths = []
    cluster_focus_report_paths = [REPO_ROOT / relpath for relpath in cluster_focus_report_relpaths]

    branch_ruling = _read_json(branch_ruling_path)
    trend = _read_json(trend_path)
    ledger = _read_json(ledger_path)
    active_cluster_focus = _read_optional_json(active_cluster_focus_path)

    policy = declaration.get("selection_policy", {})
    excluded = set(policy.get("exclude_from_blocker_facing_priority", []))
    support_lane = set(policy.get("retain_as_support_lane", []))
    required_signals = list(policy.get("required_direct_impact_signals", []))
    weights = dict(policy.get("weights", {}))

    exhausted_cluster_ids: set[str] = set()
    exhausted_cluster_summaries: dict[str, dict[str, Any]] = {}

    def _register_focus_exhaustion(payload: dict[str, Any] | None) -> None:
        if payload is None:
            return
        summary = dict(payload.get("summary", {}))
        if summary.get("selection_outcome") != "NO_ELIGIBLE_ACTIVE_CLUSTER_SURFACE":
            return
        cluster_id = str(payload.get("cluster_id", "")).strip()
        if not cluster_id:
            return
        exhausted_cluster_ids.add(cluster_id)
        exhausted_cluster_summaries[cluster_id] = summary

    _register_focus_exhaustion(active_cluster_focus)
    for path in cluster_focus_report_paths:
        _register_focus_exhaustion(_read_optional_json(path))

    candidates = list(declaration.get("candidate_clusters", []))
    ranked: list[dict[str, Any]] = []

    for candidate in candidates:
        cluster_id = str(candidate.get("cluster_id", ""))
        signals = dict(candidate.get("direct_impact_signals", {}))
        score, active_signals = _signal_score(signals, weights)
        eligible = any(bool(signals.get(sig, False)) for sig in required_signals)
        exhausted_by_active_surface_selector = cluster_id in exhausted_cluster_ids
        excluded_from_priority = (cluster_id in excluded) or exhausted_by_active_surface_selector

        ranked.append(
            {
                "cluster_id": cluster_id,
                "cluster_name": candidate.get("cluster_name"),
                "source_surfaces": candidate.get("source_surfaces", []),
                "leverage_score": score,
                "active_signals": active_signals,
                "required_signal_satisfied": eligible,
                "excluded_from_blocker_facing_priority": excluded_from_priority,
                "exhausted_by_active_surface_selector": exhausted_by_active_surface_selector,
                "retained_as_support_lane": cluster_id in support_lane,
                "priority_note": candidate.get("priority_note"),
            }
        )

    ranked_sorted = sorted(
        ranked,
        key=lambda x: (
            bool(x.get("excluded_from_blocker_facing_priority", False)),
            -int(x.get("leverage_score", 0)),
            str(x.get("cluster_id", "")),
        ),
    )

    selected = None
    for row in ranked_sorted:
        if row["excluded_from_blocker_facing_priority"]:
            continue
        if row["required_signal_satisfied"]:
            selected = row
            break

    branch_ruling_summary = branch_ruling.get("summary", {})
    theorem_gap_delta = int(trend.get("blocker_counts", {}).get("net_delta", 0) or 0)

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "branch_ruling_present": branch_ruling_path.exists(),
            "excluded_cluster_not_selected": selected is None or selected.get("cluster_id") not in excluded,
            "at_least_one_ranked_candidate_present": len(ranked_sorted) > 0,
            "selection_policy_enforced": all(sig in weights for sig in required_signals),
        },
        "objective_quality": {
            "criteria": {
                "selected_cluster_has_required_direct_signal": (
                    selected is not None and bool(selected.get("required_signal_satisfied", False))
                ),
                "selected_cluster_not_deprioritized": (
                    selected is not None and (not bool(selected.get("excluded_from_blocker_facing_priority", False)))
                ),
                "deprioritized_cluster_retained_as_support_lane": all(
                    row["retained_as_support_lane"]
                    for row in ranked_sorted
                    if row["cluster_id"] in excluded
                ),
            },
            "inputs": {
                "branch_ruling": branch_ruling_summary.get("branch_ruling"),
                "branch_allocation_decision": branch_ruling_summary.get("allocation_decision"),
            "branch_rerun_policy": branch_ruling_summary.get("rerun_policy"),
                "trend_net_delta": theorem_gap_delta,
                "progress_classification": ledger.get("progress_classification"),
                "active_cluster_focus_report_present": active_cluster_focus_path is not None and active_cluster_focus_path.exists(),
                "active_cluster_exhausted_cluster_id": None if active_cluster_focus is None else str(active_cluster_focus.get("cluster_id", "")) or None,
                "active_cluster_focus_selection_outcome": None if active_cluster_focus is None else dict(active_cluster_focus.get("summary", {})).get("selection_outcome"),
                "cluster_focus_reports": [_ptr(path) for path in cluster_focus_report_paths],
                "exhausted_cluster_ids": sorted(exhausted_cluster_ids),
                "excluded_cluster_ids": sorted(list(excluded)),
                "required_direct_impact_signals": required_signals,
                "ranked_candidates": ranked_sorted,
            },
            "summary": {
                "all_criteria_satisfied": selected is not None,
                "phase_status": "COMPLETE" if selected is not None else "INCOMPLETE",
                "next_action": (
                    "EXECUTE_SELECTED_PROOF_DEBT_CLUSTER_BOUNDED_PACKET"
                    if selected is not None
                    else "DECLARE_NO_ELIGIBLE_CLUSTER_AND_ESCALATE_ATTACK_CLASS"
                ),
            },
        },
        "summary": {
            "excluded_from_blocker_facing_priority": sorted(list(excluded)),
            "exhausted_from_active_surface_selector": sorted(exhausted_cluster_ids),
            "retained_support_lane": sorted(list(support_lane)),
            "selected_next_cluster_id": None if selected is None else selected.get("cluster_id"),
            "selected_next_cluster_name": None if selected is None else selected.get("cluster_name"),
            "selected_next_cluster_leverage_score": None if selected is None else selected.get("leverage_score"),
            "selection_outcome": (
                "NEXT_CLUSTER_SELECTED_BY_BLOCKER_LEVERAGE_FILTER"
                if selected is not None
                else "NO_ELIGIBLE_CLUSTER_UNDER_CURRENT_FILTER"
            ),
            "next_action": (
                "EXECUTE_SELECTED_PROOF_DEBT_CLUSTER_BOUNDED_PACKET"
                if selected is not None
                else "ESCALATE_TO_NEXT_SCIENCE_ATTACK_CLASS"
            ),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "branch_ruling_report": _ptr(branch_ruling_path),
            "trend": _ptr(trend_path),
            "ledger": _ptr(ledger_path),
            "active_cluster_focus_report": None if active_cluster_focus_path is None else _ptr(active_cluster_focus_path),
            "cluster_focus_reports": [_ptr(path) for path in cluster_focus_report_paths],
        },
        "non_claim_boundary": "Repository-local proof-debt next-cluster selection report; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate proof-debt next-cluster selection report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "proof_debt_next_cluster_selection_report_20260411_v0.json",
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
        "proof_debt_next_cluster_selection_report: "
        f"selection_outcome={payload['summary']['selection_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
