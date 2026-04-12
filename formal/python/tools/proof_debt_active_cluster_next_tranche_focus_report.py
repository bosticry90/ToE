from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PROOF_DEBT_ACTIVE_CLUSTER_NEXT_TRANCHE_FOCUS_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "PROOF_DEBT_ACTIVE_CLUSTER_NEXT_TRANCHE_FOCUS_20260411_v0.json"
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


def _surface_score(signals: dict[str, Any], weights: dict[str, Any]) -> tuple[int, list[str]]:
    score = 0
    active: list[str] = []
    for key, weight in weights.items():
        enabled = bool(signals.get(key, False))
        if not enabled:
            continue
        score += int(weight)
        active.append(key)
    return score, active


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)

    required_inputs = declaration.get("required_inputs", {})
    packet_report_path = REPO_ROOT / str(required_inputs.get("packet_report", ""))
    discharge_report_path = REPO_ROOT / str(required_inputs.get("discharge_tranche_report", ""))
    trend_path = REPO_ROOT / str(required_inputs.get("trend_pointer", ""))
    row_trend_path = REPO_ROOT / str(required_inputs.get("row_outcome_trend_pointer", ""))
    ledger_path = REPO_ROOT / str(required_inputs.get("ledger_pointer", ""))
    raw_surface_ruling_reports = required_inputs.get("surface_ruling_reports", [])
    if isinstance(raw_surface_ruling_reports, str):
        surface_ruling_report_relpaths = [raw_surface_ruling_reports]
    elif isinstance(raw_surface_ruling_reports, list):
        surface_ruling_report_relpaths = [str(item) for item in raw_surface_ruling_reports if str(item).strip()]
    else:
        surface_ruling_report_relpaths = []
    surface_ruling_report_paths = [REPO_ROOT / relpath for relpath in surface_ruling_report_relpaths]

    packet = _read_json(packet_report_path)
    discharge = _read_json(discharge_report_path)
    trend = _read_json(trend_path)
    row_trend = _read_json(row_trend_path)
    ledger = _read_json(ledger_path)

    declaration_cluster_id = str(declaration.get("cluster_id", ""))
    surface_rulings: dict[str, dict[str, Any]] = {}
    missing_surface_ruling_reports: list[str] = []
    ignored_surface_ruling_reports: list[str] = []
    for path in surface_ruling_report_paths:
        payload = _read_optional_json(path)
        if payload is None:
            missing_surface_ruling_reports.append(_ptr(path))
            continue
        if str(payload.get("cluster_id", "")) != declaration_cluster_id:
            ignored_surface_ruling_reports.append(_ptr(path))
            continue

        summary = payload.get("summary", {})
        target_surface = payload.get("target_surface", {})
        surface_id = str(
            summary.get("surface_id")
            or summary.get("target_surface_id")
            or target_surface.get("surface_id")
            or ""
        )
        if not surface_id:
            ignored_surface_ruling_reports.append(_ptr(path))
            continue
        surface_rulings[surface_id] = payload

    policy = declaration.get("selection_policy", {})
    required_signals = list(policy.get("required_direct_impact_signals", []))
    weights = dict(policy.get("weights", {}))

    candidates = list(declaration.get("surface_candidates", []))
    ranked: list[dict[str, Any]] = []

    for candidate in candidates:
        surface_id = str(candidate.get("surface_id", ""))
        signals = dict(candidate.get("direct_impact_signals", {}))
        score, active_signals = _surface_score(signals, weights)
        required_signal_satisfied = any(bool(signals.get(k, False)) for k in required_signals)
        surface_path = str(candidate.get("surface_path", ""))
        surface_exists = bool(surface_path) and (REPO_ROOT / surface_path).exists()
        surface_ruling = surface_rulings.get(surface_id)
        surface_ruling_summary = {} if surface_ruling is None else dict(surface_ruling.get("summary", {}))
        excluded_from_immediate_reselection = bool(
            surface_ruling_summary.get("exclude_from_immediate_reselection", False)
        )

        ranked.append(
            {
                "surface_id": surface_id,
                "surface_path": surface_path,
                "surface_kind": candidate.get("surface_kind"),
                "surface_exists": surface_exists,
                "leverage_score": score,
                "active_signals": active_signals,
                "required_signal_satisfied": required_signal_satisfied,
                "surface_ruling": surface_ruling_summary.get("surface_ruling"),
                "excluded_from_immediate_reselection": excluded_from_immediate_reselection,
                "ruling_allocation_decision": surface_ruling_summary.get("allocation_decision"),
                "priority_note": candidate.get("priority_note"),
            }
        )

    ranked_sorted = sorted(
        ranked,
        key=lambda x: (
            bool(x.get("excluded_from_immediate_reselection", False)),
            not bool(x.get("surface_exists", False)),
            -int(x.get("leverage_score", 0)),
            str(x.get("surface_id", "")),
        ),
    )

    selected = None
    for row in ranked_sorted:
        if row["excluded_from_immediate_reselection"]:
            continue
        if row["surface_exists"] and row["required_signal_satisfied"]:
            selected = row
            break

    highest_ranked_eligible = next(
        (
            row
            for row in ranked_sorted
            if (not row["excluded_from_immediate_reselection"])
            and row["surface_exists"]
            and row["required_signal_satisfied"]
        ),
        None,
    )

    theorem_delta = int(discharge.get("summary", {}).get("theorem_gap_delta", 0) or 0)
    seam_delta = int(discharge.get("summary", {}).get("seam_integration_gap_delta", 0) or 0)
    row_success = int(discharge.get("summary", {}).get("global_row_success_count", 0) or 0)

    transition_pressure = {
        "theorem_gap_delta": theorem_delta,
        "seam_integration_gap_delta": seam_delta,
        "global_row_success_count": row_success,
        "movement_observed": theorem_delta < 0 or seam_delta < 0 or row_success > 0,
    }

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "cluster_id": declaration.get("cluster_id"),
        "criteria": {
            "candidate_surfaces_present": len(ranked_sorted) > 0,
            "selected_surface_materialized": selected is not None,
            "selected_surface_exists": bool(selected and selected.get("surface_exists")),
            "selection_policy_enforced": all(k in weights for k in required_signals),
            "immediate_reselection_filter_enforced": (
                selected is None or (not bool(selected.get("excluded_from_immediate_reselection", False)))
            ),
            "active_cluster_matches_packet": (
                str(declaration.get("cluster_id", ""))
                == str(packet.get("summary", {}).get("selected_cluster_id", ""))
            ),
        },
        "objective_quality": {
            "criteria": {
                "selected_surface_has_required_direct_signal": (
                    selected is not None and bool(selected.get("required_signal_satisfied", False))
                ),
                "selected_surface_is_highest_ranked_eligible_surface": (
                    selected is not None and selected == highest_ranked_eligible
                ),
                "selection_targets_blocker_transition_pressure": not transition_pressure["movement_observed"],
            },
            "inputs": {
                "ranked_surfaces": ranked_sorted,
                "surface_ruling_reports": [_ptr(path) for path in surface_ruling_report_paths],
                "missing_surface_ruling_reports": missing_surface_ruling_reports,
                "ignored_surface_ruling_reports": ignored_surface_ruling_reports,
                "excluded_surface_ids": sorted(
                    row["surface_id"] for row in ranked_sorted if row["excluded_from_immediate_reselection"]
                ),
                "transition_pressure": transition_pressure,
                "packet_selected_cluster_id": packet.get("summary", {}).get("selected_cluster_id"),
                "discharge_tranche_state": discharge.get("summary", {}).get("tranche_state"),
                "trend_net_delta": int(trend.get("blocker_counts", {}).get("net_delta", 0) or 0),
                "progress_classification": ledger.get("progress_classification"),
                "row_outcome_counts": row_trend.get("objective_quality", {}).get("inputs", {}).get("row_outcome_counts", {}),
            },
            "summary": {
                "all_criteria_satisfied": selected is not None,
                "phase_status": "COMPLETE" if selected is not None else "INCOMPLETE",
                "next_action": (
                    "EXECUTE_SELECTED_ACTIVE_CLUSTER_SURFACE_TRANCHE"
                    if selected is not None
                    else "DECLARE_NO_ELIGIBLE_ACTIVE_SURFACE_AND_ESCALATE"
                ),
            },
        },
        "summary": {
            "selection_outcome": (
                "NEXT_ACTIVE_CLUSTER_SURFACE_SELECTED_BY_BLOCKER_LEVERAGE"
                if selected is not None
                else "NO_ELIGIBLE_ACTIVE_CLUSTER_SURFACE"
            ),
            "selected_surface_id": None if selected is None else selected.get("surface_id"),
            "selected_surface_path": None if selected is None else selected.get("surface_path"),
            "selected_surface_kind": None if selected is None else selected.get("surface_kind"),
            "selected_surface_leverage_score": None if selected is None else selected.get("leverage_score"),
            "excluded_surface_ids": sorted(
                row["surface_id"] for row in ranked_sorted if row["excluded_from_immediate_reselection"]
            ),
            "next_action": (
                "EXECUTE_SELECTED_ACTIVE_CLUSTER_SURFACE_TRANCHE"
                if selected is not None
                else "ESCALATE_ACTIVE_CLUSTER_STRATEGY"
            ),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "packet_report": _ptr(packet_report_path),
            "discharge_tranche_report": _ptr(discharge_report_path),
            "trend": _ptr(trend_path),
            "row_outcome_trend": _ptr(row_trend_path),
            "ledger": _ptr(ledger_path),
            "surface_ruling_reports": [_ptr(path) for path in surface_ruling_report_paths],
        },
        "non_claim_boundary": "Repository-local active-cluster next-tranche focus report; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate active-cluster next-tranche focus report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "proof_debt_active_cluster_next_tranche_focus_report_20260411_v0.json",
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
        "proof_debt_active_cluster_next_tranche_focus_report: "
        f"selection_outcome={payload['summary']['selection_outcome']} "
        f"selected_surface_id={payload['summary']['selected_surface_id']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
