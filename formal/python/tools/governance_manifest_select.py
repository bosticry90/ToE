from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256_joined(items: list[str]) -> str:
    payload = "\n".join(items).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _coerce_tests(raw_tests: list[object], group: str) -> list[str]:
    normalized: list[str] = []
    seen: set[str] = set()
    for item in raw_tests:
        if isinstance(item, str):
            test_path = item
        elif isinstance(item, dict):
            test_path = str(item.get("path", "")).strip()
        else:
            raise AssertionError(f"Unsupported manifest test entry type in group '{group}': {type(item)!r}")

        assert test_path, f"Manifest test path must be non-empty in group '{group}'."
        if test_path in seen:
            raise AssertionError(f"Duplicate test path in manifest group '{group}': {test_path}")
        seen.add(test_path)
        target = REPO_ROOT / test_path
        assert target.exists(), f"Manifest test path does not exist: {test_path}"
        normalized.append(test_path)
    return normalized


def load_manifest_tests(
    manifest_path: Path, group: str, tier_filter: str | None = None
) -> tuple[list[str], int | None, str | None, dict[str, int]]:
    manifest = _read_json(manifest_path)
    groups = manifest.get("groups", {})
    assert group in groups, f"Manifest group not found: {group}"
    group_payload = groups[group]

    raw_tests = group_payload.get("tests", [])
    assert isinstance(raw_tests, list) and raw_tests, "Manifest group tests must be a non-empty list."

    tests = _coerce_tests(raw_tests, group)

    test_tiers = manifest.get("test_tiers", {})
    assert isinstance(test_tiers, dict), "Manifest test_tiers must be an object when present."

    tier_counts: dict[str, int] = {}
    for test_path in tests:
        tier = str(test_tiers.get(test_path, "UNSPECIFIED"))
        tier_counts[tier] = tier_counts.get(tier, 0) + 1

    if tier_filter:
        tests = [p for p in tests if str(test_tiers.get(p, "UNSPECIFIED")) == tier_filter]
        assert tests, f"No tests matched tier '{tier_filter}' in group '{group}'."

    expected_count = group_payload.get("expected_count")
    if expected_count is not None:
        expected_count = int(expected_count)

    expected_sha = group_payload.get("expected_sha256")
    if expected_sha is not None:
        expected_sha = str(expected_sha)

    if tier_filter:
        expected_count = None
        expected_sha = None

    return tests, expected_count, expected_sha, tier_counts


def main() -> int:
    parser = argparse.ArgumentParser(description="Resolve governance pytest selection from manifest.")
    parser.add_argument("--manifest", required=True, help="Path to governance manifest JSON file.")
    parser.add_argument("--group", default="governance_pytests", help="Manifest group key to resolve.")
    parser.add_argument(
        "--tier-filter",
        default=None,
        help="Optional tier id to filter selected tests (uses manifest test_tiers mapping).",
    )
    parser.add_argument(
        "--print-summary",
        action="store_true",
        help="Print selection summary and tier distribution to stderr.",
    )
    parser.add_argument(
        "--enforce-expected",
        action="store_true",
        help="Fail if selected test count/hash differs from expected_count/expected_sha256 in manifest.",
    )
    args = parser.parse_args()

    manifest_path = (REPO_ROOT / args.manifest).resolve()
    assert manifest_path.exists(), f"Manifest file not found: {args.manifest}"

    tests, expected_count, expected_sha, tier_counts = load_manifest_tests(
        manifest_path, args.group, args.tier_filter
    )

    if args.enforce_expected:
        if expected_count is None or expected_sha is None:
            raise AssertionError(
                "--enforce-expected requires expected_count and expected_sha256 "
                f"for manifest group '{args.group}'"
            )
        if len(tests) != expected_count:
            raise AssertionError(
                f"Manifest selection count mismatch: observed={len(tests)} expected={expected_count}"
            )
        observed_sha = _sha256_joined(tests)
        if observed_sha != expected_sha:
            raise AssertionError(
                f"Manifest selection hash mismatch: observed={observed_sha} expected={expected_sha}"
            )

    if args.print_summary:
        summary_parts = [
            f"group={args.group}",
            f"selected={len(tests)}",
            f"tier_filter={args.tier_filter or 'NONE'}",
        ]
        if args.tier_filter is None:
            summary_parts.append(f"expected_count={expected_count if expected_count is not None else 'NONE'}")
        print("governance_manifest_select: " + " ".join(summary_parts), file=sys.stderr)
        if tier_counts:
            for tier in sorted(tier_counts):
                print(f"governance_manifest_select.tier.{tier}={tier_counts[tier]}", file=sys.stderr)

    for test_path in tests:
        print(test_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
