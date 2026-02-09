from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools.archive_intake_index import build_index


def _write(p: Path, data: bytes) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(data)


def test_archive_intake_index_is_deterministic(tmp_path: Path) -> None:
    repo_root = tmp_path
    archive_root = repo_root / "archive"

    _write(archive_root / "b.txt", b"hello\n")
    _write(archive_root / "a.md", b"# Title\n\nBody\n")
    _write(archive_root / "pkg" / "m.py", b"\"\"\"Docstring.\"\"\"\nX = 1\n")

    payload1 = build_index(repo_root=repo_root, roots=[archive_root])
    payload2 = build_index(repo_root=repo_root, roots=[archive_root])

    assert json.dumps(payload1, sort_keys=True) == json.dumps(payload2, sort_keys=True)

    paths = [row["path"] for row in payload1["files"]]
    assert paths == sorted(paths)

    md = next(r for r in payload1["files"] if r["path"].endswith("a.md"))
    assert md["kind"] == "markdown"
    assert md["title"] == "Title"

    py = next(r for r in payload1["files"] if r["path"].endswith("m.py"))
    assert py["kind"] == "python"
    assert py["docstring"] == "Docstring."
