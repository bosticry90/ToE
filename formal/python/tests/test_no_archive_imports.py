from __future__ import annotations

import re
from pathlib import Path


_IMPORT_ARCHIVE_RE = re.compile(r"^\s*(?:from\s+archive(?:\.|\b)|import\s+archive(?:\.|\b))")


def _repo_root_from_test_file(test_file: Path) -> Path:
    # test_file is .../ToE/formal/python/tests/test_*.py
    # parents: tests -> python -> formal -> ToE
    return test_file.resolve().parents[3]


def _should_skip_py_file(repo_root: Path, path: Path) -> bool:
    rel = path.relative_to(repo_root)
    parts = rel.parts

    # Quarantine boundary: archive is reference-only.
    if parts and parts[0] in {"archive", "scratch", "backup"}:
        return True

    # Internal pinned artifacts may include legacy reference snippets.
    if len(parts) >= 3 and parts[0] == "formal" and parts[1] == "python" and parts[2] == "artifacts":
        return True

    return False


def test_no_imports_from_archive_outside_archive() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    offenders: list[tuple[Path, int, str]] = []

    for path in repo_root.rglob("*.py"):
        if _should_skip_py_file(repo_root, path):
            continue

        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            # Non-UTF8 files are not part of the supported python surface.
            continue

        for line_no, line in enumerate(text.splitlines(), start=1):
            if _IMPORT_ARCHIVE_RE.match(line):
                offenders.append((path, line_no, line.strip()))

    assert not offenders, "Archive import(s) found outside archive quarantine:\n" + "\n".join(
        f"- {p.relative_to(repo_root)}:{ln}: {src}" for p, ln, src in offenders
    )
