from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.tools.discovery_priority_queue_report import (
    DEFAULT_CLOSURE_MAP_PATH,
    DEFAULT_DECLARATION_PATH as DEFAULT_QUEUE_DECLARATION_PATH,
    DEFAULT_LEDGER_PATH,
    DEFAULT_TREND_PATH,
    build_report as build_queue_report,
)
from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qm_stat_discovery_interpretation_report import build_report as build_interpretation_report
from formal.python.tools.qm_stat_discovery_ruling_report import build_report as build_ruling_report


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_DISCOVERY_NUMERICAL_PROBE_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_DISCOVERY_NUMERICAL_PROBE_20260411_v0.json"
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


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    probe_policy = dict(declaration.get("probe_policy", {}))

    interpretation_path = REPO_ROOT / str(required_inputs.get("discovery_interpretation_report", "")).strip()
    ruling_path = REPO_ROOT / str(required_inputs.get("discovery_ruling_report", "")).strip()
    queue_path = REPO_ROOT / str(required_inputs.get("discovery_priority_queue_report", "")).strip()

    if not queue_path.exists():
        generated_queue = build_queue_report(
            declaration_path=DEFAULT_QUEUE_DECLARATION_PATH,
            trend_path=DEFAULT_TREND_PATH,
            closure_map_path=DEFAULT_CLOSURE_MAP_PATH,
            ledger_path=DEFAULT_LEDGER_PATH,
            captured_at_utc=captured_at_utc,
        )
        queue_path.parent.mkdir(parents=True, exist_ok=True)
        queue_path.write_text(json.dumps(generated_queue, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if not ruling_path.exists():
        ruling_declaration = REPO_ROOT / "formal" / "docs" / "release" / "QM_STAT_DISCOVERY_RULING_20260411_v0.json"
        generated_ruling = build_ruling_report(
            declaration_path=ruling_declaration,
            captured_at_utc=captured_at_utc,
        )
        ruling_path.parent.mkdir(parents=True, exist_ok=True)
        ruling_path.write_text(json.dumps(generated_ruling, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if not interpretation_path.exists():
        interpretation_declaration = (
            REPO_ROOT
            / "formal"
            / "docs"
            / "release"
            / "QM_STAT_DISCOVERY_INTERPRETATION_20260411_v0.json"
        )
        generated_interpretation = build_interpretation_report(
            declaration_path=interpretation_declaration,
            captured_at_utc=captured_at_utc,
        )
        interpretation_path.parent.mkdir(parents=True, exist_ok=True)
        interpretation_path.write_text(json.dumps(generated_interpretation, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    interpretation = _read_json(interpretation_path)
    ruling = _read_json(ruling_path)
    queue = _read_json(queue_path)

    interpretation_summary = dict(interpretation.get("summary", {}))
    ruling_summary = dict(ruling.get("summary", {}))
    queue_summary = dict(queue.get("summary", {}))

    target_row = str(probe_policy.get("target_row", "")).strip()
    top_rank_row = str(queue_summary.get("top_rank_row", "")).strip()
    interpretation_value = str(interpretation_summary.get("interpretation", "")).strip()
    ruling_value = str(ruling_summary.get("ruling", "")).strip()

    seam_alignment = target_row == top_rank_row == str(interpretation_summary.get("target_row", "")).strip()
    bounded_cycle_count = int(probe_policy.get("max_probe_cycles", 1))

    probe_runnable = (
        seam_alignment
        and bounded_cycle_count == 1
        and ruling_value == "DISCRIMINATOR_PRODUCED"
        and interpretation_value in {"INTERNAL_DISCRIMINATIVE_ONLY", "EXTERNALLY_COMPARABLE", "NUMERICAL_PROBE_READY"}
    )

    if probe_runnable:
        probe_lane_status = "BOUNDED_PROBE_LANE_READY"
        next_action = "EXECUTE_ONE_NUMERICAL_PROBE_CYCLE_ON_ROW_SEAM"
    else:
        probe_lane_status = "BOUNDED_PROBE_LANE_BLOCKED"
        next_action = "RECONCILE_SEAM_ALIGNMENT_OR_RULING_PRECONDITIONS"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "summary": {
            "target_row": target_row,
            "top_rank_row": top_rank_row,
            "seam_alignment": seam_alignment,
            "ruling": ruling_value,
            "interpretation": interpretation_value,
            "max_probe_cycles": bounded_cycle_count,
            "probe_lane_status": probe_lane_status,
            "probe_runnable": probe_runnable,
            "shadow_mode_required": bool(probe_policy.get("shadow_mode_required", True)),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "discovery_interpretation_report": _ptr(interpretation_path),
            "discovery_ruling_report": _ptr(ruling_path),
            "discovery_priority_queue_report": _ptr(queue_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT discovery numerical probe report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate QM-STAT discovery numerical probe report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_discovery_numerical_probe_report_20260411_v0.json",
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
        "qm_stat_discovery_numerical_probe_report: "
        f"probe_lane_status={payload['summary']['probe_lane_status']} "
        f"probe_runnable={payload['summary']['probe_runnable']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
