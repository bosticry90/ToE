from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = _find_repo_root(Path(__file__))


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256_joined(items: list[str]) -> str:
    payload = "\n".join(items).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def load_manifest_tests(manifest_path: Path, group: str) -> tuple[list[str], int | None, str | None]:
    manifest = _read_json(manifest_path)
    groups = manifest.get("groups", {})
    assert group in groups, f"Manifest group not found: {group}"
    group_payload = groups[group]

    tests = group_payload.get("tests", [])
    assert isinstance(tests, list) and tests, "Manifest group tests must be a non-empty list."

    normalized: list[str] = []
    seen: set[str] = set()
    for test_path in tests:
        assert isinstance(test_path, str) and test_path, "Each manifest test path must be a non-empty string."
        if test_path in seen:
            raise AssertionError(f"Duplicate test path in manifest group '{group}': {test_path}")
        seen.add(test_path)
        target = REPO_ROOT / test_path
        assert target.exists(), f"Manifest test path does not exist: {test_path}"
        normalized.append(test_path)

    expected_count = group_payload.get("expected_count")
    if expected_count is not None:
        expected_count = int(expected_count)

    expected_sha = group_payload.get("expected_sha256")
    if expected_sha is not None:
        expected_sha = str(expected_sha)

    return normalized, expected_count, expected_sha


def main() -> int:
    parser = argparse.ArgumentParser(description="Resolve governance pytest selection from manifest.")
    parser.add_argument("--manifest", required=True, help="Path to governance manifest JSON file.")
    parser.add_argument("--group", default="governance_pytests", help="Manifest group key to resolve.")
    parser.add_argument(
        "--enforce-expected",
        action="store_true",
        help="Fail if selected test count/hash differs from expected_count/expected_sha256 in manifest.",
    )
    args = parser.parse_args()

    manifest_path = (REPO_ROOT / args.manifest).resolve()
    assert manifest_path.exists(), f"Manifest file not found: {args.manifest}"

    tests, expected_count, expected_sha = load_manifest_tests(manifest_path, args.group)

    if args.enforce_expected:
        if expected_count is not None and len(tests) != expected_count:
            raise AssertionError(
                f"Manifest selection count mismatch: observed={len(tests)} expected={expected_count}"
            )
        observed_sha = _sha256_joined(tests)
        if expected_sha is not None and observed_sha != expected_sha:
            raise AssertionError(
                f"Manifest selection hash mismatch: observed={observed_sha} expected={expected_sha}"
            )

    for test_path in tests:
        print(test_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
