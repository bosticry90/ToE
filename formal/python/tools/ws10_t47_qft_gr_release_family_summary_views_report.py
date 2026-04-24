from __future__ import annotations

import argparse
import json
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "WS10_T47_QFT_GR_RELEASE_FAMILY_SUMMARY_VIEWS_REPORT_20260418_v0"
DEFAULT_OUT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "qft_gr_sliceb_increment_family_summary_views_20260418_v0.json"
REGISTRY_PATH = REPO_ROOT / "formal" / "output" / "reports" / "qft_gr_sliceb_increment_family_registry_20260418_v0.json"


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _range_bands(values: list[int]) -> list[dict[str, int]]:
    if not values:
        return []
    sorted_values = sorted(set(values))
    bands: list[dict[str, int]] = []
    start = sorted_values[0]
    end = start
    for value in sorted_values[1:]:
        if value == end + 1:
            end = value
            continue
        bands.append({"start": start, "end": end})
        start = value
        end = value
    bands.append({"start": start, "end": end})
    return bands


def build_report(*, captured_at_utc: str | None = None) -> dict[str, Any]:
    registry = _read_json(REGISTRY_PATH)
    entries = registry.get("entries", [])

    increment_files: dict[int, dict[str, str]] = defaultdict(dict)
    kind_increments: dict[str, list[int]] = defaultdict(list)
    synthesis_endpoints: list[int] = []
    synthesis_starts: list[int] = []
    for entry in entries:
        kind = entry["kind"]
        if "increment" in entry:
            increment = int(entry["increment"])
            increment_files[increment][kind] = entry["file"]
            kind_increments[kind].append(increment)
        if kind == "SYNTHESIS_NOTE":
            synthesis_endpoints.append(int(entry["end_increment"]))
            synthesis_starts.append(int(entry["start_increment"]))

    all_increments = sorted(increment_files)
    banded_increment_views = []
    if all_increments:
        band_start = all_increments[0]
        previous = band_start
        previous_kinds = tuple(sorted(increment_files[band_start]))
        for increment in all_increments[1:]:
            current_kinds = tuple(sorted(increment_files[increment]))
            if increment == previous + 1 and current_kinds == previous_kinds:
                previous = increment
                continue
            banded_increment_views.append(
                {
                    "start_increment": band_start,
                    "end_increment": previous,
                    "available_kinds": list(previous_kinds),
                }
            )
            band_start = increment
            previous = increment
            previous_kinds = current_kinds
        banded_increment_views.append(
            {
                "start_increment": band_start,
                "end_increment": previous,
                "available_kinds": list(previous_kinds),
            }
        )

    endpoint_min = registry.get("synthesis_span", {}).get("min_end_increment")
    endpoint_max = registry.get("synthesis_span", {}).get("max_end_increment")
    endpoint_range = set(range(int(endpoint_min), int(endpoint_max) + 1)) if endpoint_min and endpoint_max else set()
    missing_synthesis_endpoints = sorted(endpoint_range.difference(synthesis_endpoints))

    terminal_increments = all_increments[-10:]
    terminal_increment_view = [
        {
            "increment": increment,
            "available_kinds": sorted(increment_files[increment]),
            "files_by_kind": dict(sorted(increment_files[increment].items())),
        }
        for increment in terminal_increments
    ]

    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": "qft_gr_sliceb_increment_family_summary_views_20260418_v0",
        "status": "DERIVED_NONAUTHORITATIVE_REVIEW_SURFACE_v0",
        "captured_at_utc": _ts(captured_at_utc),
        "derived_from": {
            "registry_pointer": _ptr(REGISTRY_PATH),
            "family_id": registry.get("family_id"),
            "registry_file_count": int(registry.get("file_count", 0)),
        },
        "kind_span_views": {
            "ASSESSMENT_NOTE": {
                "count": len(kind_increments.get("ASSESSMENT_NOTE", [])),
                "increment_bands": _range_bands(kind_increments.get("ASSESSMENT_NOTE", [])),
            },
            "EXECUTION_PACKET": {
                "count": len(kind_increments.get("EXECUTION_PACKET", [])),
                "increment_bands": _range_bands(kind_increments.get("EXECUTION_PACKET", [])),
            },
            "SEMANTIC_DELTA_DECISION_NOTE": {
                "count": len(kind_increments.get("SEMANTIC_DELTA_DECISION_NOTE", [])),
                "increment_bands": _range_bands(kind_increments.get("SEMANTIC_DELTA_DECISION_NOTE", [])),
            },
            "SCIENCE_VALIDATION_NOTE": {
                "count": len(kind_increments.get("SCIENCE_VALIDATION_NOTE", [])),
                "increment_bands": _range_bands(kind_increments.get("SCIENCE_VALIDATION_NOTE", [])),
            },
            "SYNTHESIS_NOTE": {
                "count": len(synthesis_endpoints),
                "start_increment_bands": _range_bands(synthesis_starts),
                "end_increment_bands": _range_bands(synthesis_endpoints),
                "missing_end_increments": missing_synthesis_endpoints,
            },
        },
        "banded_increment_views": banded_increment_views,
        "terminal_increment_view": terminal_increment_view,
        "review_focus": {
            "semantic_activation_band": {"start_increment": 5, "end_increment": 49},
            "science_validation_band": {"start_increment": 50, "end_increment": 68},
            "terminal_increment_band": {"start_increment": terminal_increments[0], "end_increment": terminal_increments[-1]} if terminal_increments else None,
            "synthesis_anchor_distribution": {
                "start_increments": sorted(set(synthesis_starts)),
                "all_synthesis_notes_anchor_at_increment01": sorted(set(synthesis_starts)) == [1],
            },
        },
        "operator_boundary": {
            "authority_status": "DERIVED_SUMMARY_ONLY",
            "active_review_surface": "SUMMARY_VIEWS_OVER_T43_REGISTRY",
            "non_claim_boundary": "These summary views are derived from the T43 registry and do not replace the registry or underlying release notes as authority sources.",
        },
        "summary": {
            "terminal_outcome": "QFT_GR_SLICEB_RELEASE_FAMILY_SUMMARY_VIEWS_GENERATED_OVER_T43_REGISTRY",
            "next_action": "USE_QFT_GR_SUMMARY_VIEWS_AS_ACTIVE_REVIEW_SURFACE_AND_DEFER_RAW_CHAIN_TO_ARCHIVAL_TRACEABILITY",
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate the WS-10 T47 QFT-GR release-family summary views artifact.")
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    args = parser.parse_args()

    report = build_report()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()