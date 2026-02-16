from __future__ import annotations

from pathlib import Path
import re


def test_governance_suite_has_no_duplicate_test_entries() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    suite_path = repo_root / "governance_suite.ps1"
    text = suite_path.read_text(encoding="utf-8")
    pattern = re.compile(r"formal/python/tests/[A-Za-z0-9_./-]+\.py")

    seen: dict[str, list[int]] = {}
    for line_no, line in enumerate(text.splitlines(), start=1):
        for match in pattern.findall(line):
            normalized = match.replace("\\", "/")
            seen.setdefault(normalized, []).append(line_no)

    assert seen, "No test paths found in governance_suite.ps1."

    duplicates = {path: line_nos for path, line_nos in seen.items() if len(line_nos) > 1}
    assert duplicates == {}, (
        "Duplicate test entries found in governance_suite.ps1:\n"
        + "\n".join(f"{path} @ lines {line_nos}" for path, line_nos in sorted(duplicates.items()))
    )

    missing = [path for path in seen if not (repo_root / path).exists()]
    assert missing == [], "Suite references missing test files:\n" + "\n".join(sorted(missing))
