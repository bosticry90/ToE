from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PHYS_MATH_THROUGHPUT_BASELINE_v0"
DEFAULT_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_math_throughput_baseline_20260407_v0.json"

METADATA_REGEXES = [
    re.compile(r"_extract_token\("),
    re.compile(r"decision_record_pointer"),
    re.compile(r"status_tokens"),
    re.compile(r"assert\s+.*\s+in\s+.*text"),
]

SCIENCE_REGEXES = [
    re.compile(r"Fraction\("),
    re.compile(r"\bnp\."),
    re.compile(r"\bnumpy\b"),
    re.compile(r"\bsympy\b"),
    re.compile(r"\bresidual\b"),
    re.compile(r"\beigen\b"),
    re.compile(r"\bsimulation\b"),
    re.compile(r"\bintegral\b"),
    re.compile(r"\bcurve_fit\b"),
    re.compile(r"\bfft\b"),
    re.compile(r"\blinarith\b"),
]


def _read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _iter_test_files() -> list[Path]:
    tests_dir = REPO_ROOT / "formal" / "python" / "tests"
    return sorted(tests_dir.glob("test_*.py"))


def _match_counts(files: list[Path], patterns: list[re.Pattern[str]]) -> tuple[int, int]:
    file_count = 0
    line_count = 0
    for path in files:
        text = _read_text(path)
        matched_line = False
        for line in text.splitlines():
            if any(p.search(line) for p in patterns):
                line_count += 1
                matched_line = True
        if matched_line:
            file_count += 1
    return file_count, line_count


def _load_manifest() -> dict[str, Any]:
    manifest_path = REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_TEST_MANIFEST_v1.json"
    return json.loads(_read_text(manifest_path))


def build_snapshot_payload(*, generated_at_utc: str | None = None) -> dict[str, Any]:
    files = _iter_test_files()

    metadata_file_count, metadata_line_count = _match_counts(files, METADATA_REGEXES)
    science_file_count, science_line_count = _match_counts(files, SCIENCE_REGEXES)

    manifest = _load_manifest()
    governance_group = manifest.get("groups", {}).get("governance_pytests", {})
    governance_tests = governance_group.get("tests", [])

    output = {
        "schema_id": SCHEMA_ID,
        "generated_at_utc": generated_at_utc or datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "status": "BASELINE_CAPTURED_NONCLAIM",
        "baseline_context": {
            "goal": "Quantify governance-overhead vs science-signal mix before refactors.",
            "scope": "formal/python/tests and governance manifest governance_pytests group.",
            "nonclaim_boundary": "Measurement-only artifact; no theorem or claim adjudication.",
        },
        "counts": {
            "total_test_files": len(files),
            "metadata_pattern_file_count": metadata_file_count,
            "metadata_pattern_line_count": metadata_line_count,
            "science_pattern_file_count": science_file_count,
            "science_pattern_line_count": science_line_count,
            "governance_manifest_expected_count": governance_group.get("expected_count"),
            "governance_manifest_listed_count": len(governance_tests),
        },
        "ratios": {
            "metadata_to_science_file_ratio": (
                round(metadata_file_count / science_file_count, 4)
                if science_file_count > 0
                else None
            ),
            "metadata_to_science_line_ratio": (
                round(metadata_line_count / science_line_count, 4)
                if science_line_count > 0
                else None
            ),
        },
        "pattern_registry": {
            "metadata_patterns": [p.pattern for p in METADATA_REGEXES],
            "science_patterns": [p.pattern for p in SCIENCE_REGEXES],
        },
        "sources": {
            "tests_root": "formal/python/tests",
            "manifest": "formal/docs/release/GOVERNANCE_TEST_MANIFEST_v1.json",
            "manifest_group": "governance_pytests",
        },
    }
    return output


def build_snapshot(report_path: Path, *, generated_at_utc: str | None = None) -> dict[str, Any]:
    output = build_snapshot_payload(generated_at_utc=generated_at_utc)
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    return output


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Capture throughput baseline metrics for governance-vs-science signal mix."
    )
    parser.add_argument(
        "--report",
        type=Path,
        default=DEFAULT_REPORT_PATH,
        help="Output report path.",
    )
    parser.add_argument(
        "--generated-at-utc",
        default=None,
        help="Override generated_at_utc for deterministic refreshes.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    report_path = (REPO_ROOT / ns.report).resolve() if not ns.report.is_absolute() else ns.report
    payload = build_snapshot(report_path, generated_at_utc=ns.generated_at_utc)
    counts = payload["counts"]
    print(
        "throughput_baseline: "
        f"tests={counts['total_test_files']} "
        f"metadata_files={counts['metadata_pattern_file_count']} "
        f"science_files={counts['science_pattern_file_count']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
