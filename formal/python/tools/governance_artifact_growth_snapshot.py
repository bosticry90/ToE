from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
BASELINE_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_artifact_growth_baseline_20260410_v0.json"
SCHEMA_ID = "GOVERNANCE_ARTIFACT_GROWTH_SNAPSHOT_20260410_v0"


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _count_json_files(path: Path) -> int:
    if not path.exists():
        return 0
    return sum(1 for candidate in path.rglob("*.json") if candidate.is_file())


def build_snapshot(*, output_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    baseline = _read_json(BASELINE_PATH)
    baseline_counts = baseline.get("baseline_counts", {})
    if not isinstance(baseline_counts, dict):
        baseline_counts = {}

    current_output = _count_json_files(REPO_ROOT / "formal" / "output")
    current_reports = _count_json_files(REPO_ROOT / "formal" / "output" / "reports")

    base_output = int(baseline_counts.get("json_files_under_formal_output", 0))
    base_reports = int(baseline_counts.get("json_files_under_formal_output_reports", 0))

    payload = {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc
        or datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "current_counts": {
            "json_files_under_formal_output": current_output,
            "json_files_under_formal_output_reports": current_reports,
        },
        "delta_vs_baseline": {
            "json_files_under_formal_output": current_output - base_output,
            "json_files_under_formal_output_reports": current_reports - base_reports,
        },
        "non_claim_boundary": "Operational artifact growth snapshot only; no theorem or closure claim.",
    }

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Capture artifact-growth snapshot relative to pinned baseline.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "governance_artifact_growth_snapshot_20260410_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out_path = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_snapshot(output_path=out_path, captured_at_utc=ns.captured_at_utc)
    current = payload["current_counts"]
    delta = payload["delta_vs_baseline"]
    print(
        "governance_artifact_growth_snapshot: "
        f"output={current['json_files_under_formal_output']} "
        f"reports={current['json_files_under_formal_output_reports']} "
        f"delta_output={delta['json_files_under_formal_output']} "
        f"delta_reports={delta['json_files_under_formal_output_reports']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
