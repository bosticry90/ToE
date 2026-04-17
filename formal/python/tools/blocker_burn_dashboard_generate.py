from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "BLOCKER_BURN_DASHBOARD_20260416_v0"

COMPLETION_MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md"
TREND_WINDOW_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json"
CLOSURE_MAP_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_closure_map_20260410_v0.json"
LEDGER_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json"
BASELINE_PACK_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "convergence_baseline_pack_20260409_v0.json"

BLOCKER_CLASSES = (
    "THEOREM_GAP",
    "SEAM_INTEGRATION_GAP",
    "PARITY_DRIFT",
    "GOVERNANCE_GUARDRAIL",
    "EVIDENCE_ALIGNMENT_GAP",
)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _resolve_timestamp(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _parse_completion_rows(matrix_path: Path) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for line in _read_text(matrix_path).splitlines():
        if not line.startswith("| ROW-"):
            continue
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if len(cells) < 8:
            continue
        rows.append(
            {
                "row_id": cells[0],
                "domain": cells[1],
                "lane": cells[2],
                "current_status": cells[3],
                "blocker_class": cells[4],
                "primary_target": cells[5],
                "primary_artifact": cells[6],
                "primary_gate": cells[7],
            }
        )
    if not rows:
        raise ValueError("Completion matrix produced zero canonical rows.")
    return rows


def _parse_matrix_date(matrix_text: str) -> str | None:
    match = re.search(r"(?m)^- Date:\s*(\d{4}-\d{2}-\d{2})\s*$", matrix_text)
    if not match:
        return None
    return f"{match.group(1)}T00:00:00Z"


def _delta_by_class(prior: dict[str, Any], current: dict[str, Any]) -> dict[str, int]:
    delta: dict[str, int] = {}
    for blocker_class in BLOCKER_CLASSES:
        delta[blocker_class] = int(current.get(blocker_class, 0) or 0) - int(prior.get(blocker_class, 0) or 0)
    return delta


def _movement_status(net_delta: int) -> str:
    if net_delta < 0:
        return "DECREASING"
    if net_delta == 0:
        return "FLAT"
    return "INCREASING"


def _row_blocker_contributions(rows: list[dict[str, str]]) -> dict[str, Any]:
    contributions: dict[str, dict[str, Any]] = {
        blocker_class: {"row_count": 0, "row_ids": []} for blocker_class in BLOCKER_CLASSES
    }
    for row in rows:
        blocker_class = row["blocker_class"]
        entry = contributions.setdefault(blocker_class, {"row_count": 0, "row_ids": []})
        entry["row_count"] += 1
        entry["row_ids"].append(row["row_id"])

    for blocker_class in contributions:
        contributions[blocker_class]["row_ids"] = sorted(contributions[blocker_class]["row_ids"])

    return {
        "rows_total": len(rows),
        "blocker_classes": contributions,
    }


def _row_promotion_readiness(rows: list[dict[str, str]]) -> dict[str, Any]:
    readiness_rows: list[dict[str, Any]] = []
    for row in rows:
        target_path = REPO_ROOT / row["primary_target"]
        artifact_path = REPO_ROOT / row["primary_artifact"]
        gate_path = REPO_ROOT / row["primary_gate"]

        target_exists = target_path.exists()
        artifact_exists = artifact_path.exists()
        gate_exists = gate_path.exists()
        all_paths_pinned = target_exists and artifact_exists and gate_exists

        readiness_rows.append(
            {
                "row_id": row["row_id"],
                "domain": row["domain"],
                "lane": row["lane"],
                "blocker_class": row["blocker_class"],
                "current_status": row["current_status"],
                "target_surface_pinned": target_exists,
                "artifact_pinned": artifact_exists,
                "gate_path_pinned": gate_exists,
                "promotion_readiness_status": (
                    "PATHS_PINNED_PENDING_GATE_RUNTIME_AND_PARITY_EVIDENCE"
                    if all_paths_pinned
                    else "BLOCKED_MISSING_CANONICAL_PATH"
                ),
            }
        )

    pinned_count = sum(
        1
        for row in readiness_rows
        if row["target_surface_pinned"] and row["artifact_pinned"] and row["gate_path_pinned"]
    )

    return {
        "rows_total": len(readiness_rows),
        "rows_with_all_paths_pinned": pinned_count,
        "rows_pending_gate_runtime_or_parity": pinned_count,
        "rows_missing_canonical_path": len(readiness_rows) - pinned_count,
        "rows": readiness_rows,
        "promotion_rule_reference": "PROMOTED_ONLY_WHEN_TARGET_ARTIFACT_GATE_AND_PARITY_ARE_ALL_SATISFIED",
        "report_scope_boundary": "DASHBOARD_REPORTS_PATH_READINESS_ONLY_AND_DOES_NOT_ASSERT_GATE_PASSING",
    }


def _closure_map_linkage(closure_map: dict[str, Any]) -> dict[str, Any]:
    mappings = closure_map.get("mappings", [])
    if not isinstance(mappings, list):
        mappings = []
    return {
        "rows_total": int(closure_map.get("rows_total", 0) or 0),
        "missing_owner_rows": sorted(str(row) for row in closure_map.get("missing_owner_rows", [])),
        "mapped_rows": [
            {
                "row_id": str(mapping.get("row_id", "")),
                "blocker_class": str(mapping.get("blocker_class", "")),
                "exit_criterion": str(mapping.get("exit_criterion", "")),
                "closure_gate": str(mapping.get("closure_gate", "")),
                "required_closure_artifact": str(mapping.get("required_closure_artifact", "")),
            }
            for mapping in mappings
        ],
    }


def _freshness_entry(*, source: str, captured_at_utc: str | None, newest_epoch: float | None) -> dict[str, Any]:
    if not captured_at_utc:
        return {
            "source": source,
            "captured_at_utc": None,
            "freshness_status": "TIMESTAMP_UNAVAILABLE",
            "age_vs_newest_seconds": None,
        }

    captured_dt = datetime.strptime(captured_at_utc, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)
    age = 0 if newest_epoch is None else int(newest_epoch - captured_dt.timestamp())
    status = "CURRENT_MAX_CAPTURE" if age == 0 else "STALE_AGAINST_NEWEST_CAPTURE"
    return {
        "source": source,
        "captured_at_utc": captured_at_utc,
        "freshness_status": status,
        "age_vs_newest_seconds": age,
    }


def _source_freshness(*, matrix_text: str, trend_window: dict[str, Any], closure_map: dict[str, Any], ledger: dict[str, Any], baseline_pack: dict[str, Any]) -> dict[str, Any]:
    timestamps = {
        _ptr(COMPLETION_MATRIX_PATH): _parse_matrix_date(matrix_text),
        _ptr(TREND_WINDOW_REPORT_PATH): str(trend_window.get("captured_at_utc") or "") or None,
        _ptr(CLOSURE_MAP_REPORT_PATH): str(closure_map.get("captured_at_utc") or "") or None,
        _ptr(LEDGER_REPORT_PATH): str(ledger.get("captured_at_utc") or "") or None,
        _ptr(BASELINE_PACK_REPORT_PATH): str(baseline_pack.get("captured_at_utc") or "") or None,
    }
    epochs = []
    for value in timestamps.values():
        if not value:
            continue
        dt = datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)
        epochs.append(dt.timestamp())
    newest_epoch = max(epochs) if epochs else None

    entries = [
        _freshness_entry(source=source, captured_at_utc=captured_at_utc, newest_epoch=newest_epoch)
        for source, captured_at_utc in timestamps.items()
    ]
    stale_sources = [entry["source"] for entry in entries if entry["freshness_status"] == "STALE_AGAINST_NEWEST_CAPTURE"]
    return {
        "entries": entries,
        "newest_capture_utc": None if newest_epoch is None else datetime.fromtimestamp(newest_epoch, tz=timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "stale_sources": stale_sources,
        "stale_input_warning": bool(stale_sources),
    }


def build_dashboard(*, output_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    matrix_text = _read_text(COMPLETION_MATRIX_PATH)
    rows = _parse_completion_rows(COMPLETION_MATRIX_PATH)
    trend_window = _read_json(TREND_WINDOW_REPORT_PATH)
    closure_map = _read_json(CLOSURE_MAP_REPORT_PATH)
    ledger = _read_json(LEDGER_REPORT_PATH)
    baseline_pack = _read_json(BASELINE_PACK_REPORT_PATH)

    blocker_counts = dict(trend_window.get("blocker_counts", {}))
    prior = dict(blocker_counts.get("prior", {}))
    current = dict(blocker_counts.get("current", {}))
    net_delta = int(blocker_counts.get("net_delta", 0) or 0)
    delta_by_class = _delta_by_class(prior, current)
    movement_status = _movement_status(net_delta)

    exception_requirement = dict(trend_window.get("exception_requirement", {}))
    closure_linkage = _closure_map_linkage(closure_map)

    payload = {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _resolve_timestamp(captured_at_utc),
        "window": trend_window.get("window", {}),
        "tranche_id": trend_window.get("tranche_id"),
        "blocker_scoreboard": {
            "prior": prior,
            "current": current,
            "delta_by_class": delta_by_class,
            "net_delta": net_delta,
            "movement_status": movement_status,
            "window_rule": "AT_LEAST_ONE_BLOCKER_CLASS_MUST_DECREASE_WITHIN_EACH_8_TRANCHE_WINDOW",
            "exception_required": bool(exception_requirement.get("exception_required", net_delta >= 0)),
            "exception_artifact_pointer": exception_requirement.get("exception_artifact_pointer"),
            "movement_authority": _ptr(TREND_WINDOW_REPORT_PATH),
        },
        "row_blocker_contributions": _row_blocker_contributions(rows),
        "row_promotion_readiness": _row_promotion_readiness(rows),
        "closure_map_linkage": closure_linkage,
        "tranche_timeline": {
            "window": trend_window.get("window", {}),
            "current_tranche_id": trend_window.get("tranche_id"),
            "row_promotion_count": int(_read_json(REPO_ROOT / "formal" / "output" / "ws10_tgc76_row_promotion_blocker_burn_review_checkpoint_20260408_v0.json").get("row_promotion_count", 0) or 0),
            "next_action": str(_read_json(REPO_ROOT / "formal" / "output" / "ws10_tgc76_row_promotion_blocker_burn_review_checkpoint_20260408_v0.json").get("next_action", "")),
            "ledger_progress_classification": str(ledger.get("progress_classification", "")),
            "ledger_blocker_state_change": str(ledger.get("actual_blocker_state_change", "")),
        },
        "source_freshness": _source_freshness(
            matrix_text=matrix_text,
            trend_window=trend_window,
            closure_map=closure_map,
            ledger=ledger,
            baseline_pack=baseline_pack,
        ),
        "source_bundle": {
            "completion_matrix": _ptr(COMPLETION_MATRIX_PATH),
            "trend_window_report": _ptr(TREND_WINDOW_REPORT_PATH),
            "closure_map_report": _ptr(CLOSURE_MAP_REPORT_PATH),
            "physics_progress_ledger": _ptr(LEDGER_REPORT_PATH),
            "convergence_baseline_pack": _ptr(BASELINE_PACK_REPORT_PATH),
        },
        "non_claim_boundary": "This dashboard is a repository-local blocker-burn planning artifact and does not assert scientific adequacy or row promotion by itself.",
    }

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate canonical blocker-burn dashboard report.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json",
        help="Output path for blocker-burn dashboard report JSON.",
    )
    parser.add_argument(
        "--captured-at-utc",
        default=None,
        help="Optional RFC3339 UTC timestamp override.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    output_path = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_dashboard(output_path=output_path, captured_at_utc=ns.captured_at_utc)
    print(
        "blocker_burn_dashboard_generate: "
        f"movement={payload['blocker_scoreboard']['movement_status']} "
        f"stale_sources={len(payload['source_freshness']['stale_sources'])} "
        f"out={output_path}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())