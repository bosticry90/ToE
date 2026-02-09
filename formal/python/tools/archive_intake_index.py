from __future__ import annotations

"""Archive Intake Index (quarantine-safe).

Goal
- Deterministically inventory legacy materials under `archive/`.
- Produce a machine-readable index for triage/dossier creation.

Policy alignment
- Read-only: does not import from `archive/`.
- Bookkeeping only: no epistemic status changes.

Output schema (v1)
{
  "schema_version": 1,
  "roots": ["archive"],
  "files": [
    {
      "path": "archive/.../file.ext",
      "sha256": "...",
      "bytes": 123,
      "kind": "python|markdown|text|binary",
      "title": "..." | null,
      "docstring": "..." | null
    }
  ]
}
"""

if __name__ == "__main__" and (__package__ is None or __package__ == ""):
    from pathlib import Path as _Path

    _tool = _Path(__file__).stem
    raise SystemExit(
        "Do not run this tool as a script.\n"
        "Run it as a module so package imports resolve.\n\n"
        f"  .\\py.ps1 -m formal.python.tools.{_tool} --help\n"
    )

import argparse
import ast
import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Optional


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _sha256_path(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _rel(repo_root: Path, p: Path) -> str:
    try:
        return p.resolve().relative_to(repo_root.resolve()).as_posix()
    except Exception:
        return p.as_posix()


_TEXT_EXTS = {
    ".md",
    ".txt",
    ".py",
    ".lean",
    ".toml",
    ".yaml",
    ".yml",
    ".json",
    ".ini",
    ".cfg",
    ".csv",
    ".tex",
    ".rst",
}


def _kind_for_path(p: Path) -> str:
    ext = p.suffix.lower()
    if ext == ".py":
        return "python"
    if ext == ".md":
        return "markdown"
    if ext in _TEXT_EXTS:
        return "text"
    return "binary"


def _read_text_best_effort(p: Path, limit: int = 32_768) -> str:
    data = p.read_bytes()
    if len(data) > limit:
        data = data[:limit]
    return data.decode("utf-8", errors="replace")


def _extract_markdown_title(text: str) -> Optional[str]:
    for line in text.splitlines():
        s = line.strip()
        if not s:
            continue
        if s.startswith("#"):
            return s.lstrip("#").strip()[:200] or None
        return s[:200] or None
    return None


def _extract_python_docstring(text: str) -> Optional[str]:
    try:
        module = ast.parse(text)
    except SyntaxError:
        return None
    doc = ast.get_docstring(module)
    if not doc:
        return None
    doc = doc.strip().replace("\r\n", "\n")
    if len(doc) > 2000:
        doc = doc[:2000] + "…"
    return doc


@dataclass(frozen=True)
class IndexRow:
    path: str
    sha256: str
    bytes: int
    kind: str
    title: Optional[str]
    docstring: Optional[str]


def _iter_files(root: Path) -> Iterable[Path]:
    if root.is_file():
        yield root
        return
    if not root.exists():
        return
    paths = sorted([p for p in root.rglob("*") if p.is_file()])
    for p in paths:
        yield p


def build_index(repo_root: Path, roots: list[Path]) -> dict:
    rows: list[IndexRow] = []

    for root in roots:
        for p in _iter_files(root):
            rel = _rel(repo_root, p)
            kind = _kind_for_path(p)

            title: Optional[str] = None
            docstring: Optional[str] = None
            if kind in {"python", "markdown", "text"}:
                text = _read_text_best_effort(p)
                if kind == "markdown":
                    title = _extract_markdown_title(text)
                elif kind == "python":
                    docstring = _extract_python_docstring(text)

            rows.append(
                IndexRow(
                    path=rel,
                    sha256=_sha256_path(p),
                    bytes=p.stat().st_size,
                    kind=kind,
                    title=title,
                    docstring=docstring,
                )
            )

    rows = sorted(rows, key=lambda r: r.path)

    return {
        "schema_version": 1,
        "roots": [
            _rel(repo_root, r) if r.exists() else r.as_posix() for r in sorted(roots)
        ],
        "files": [
            {
                "path": r.path,
                "sha256": r.sha256,
                "bytes": r.bytes,
                "kind": r.kind,
                "title": r.title,
                "docstring": r.docstring,
            }
            for r in rows
        ],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Write a deterministic archive intake index.")
    parser.add_argument(
        "--roots",
        nargs="+",
        default=["archive"],
        help="One or more repo-relative roots to inventory (default: archive)",
    )
    parser.add_argument(
        "--out",
        default="formal/output/archive_intake_index.json",
        help="Repo-relative output JSON path",
    )

    args = parser.parse_args(argv)

    repo_root = _find_repo_root(Path(__file__))
    roots = [repo_root / r for r in args.roots]
    payload = build_index(repo_root=repo_root, roots=roots)

    out_path = repo_root / args.out
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
