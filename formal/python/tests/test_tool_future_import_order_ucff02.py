from __future__ import annotations

from pathlib import Path


def _strip_leading_trivia(lines: list[str]) -> list[str]:
    out: list[str] = []
    for line in lines:
        s = line.strip()
        if not s:
            continue
        if s.startswith("#"):
            continue
        out.append(line)
    return out


def test_ovucff02_tool_future_import_is_immediately_after_docstring() -> None:
    path = Path("formal/python/tools/ovucff02_framewise_variation_audit.py")
    lines = path.read_text(encoding="utf-8").splitlines()

    # Allow shebang/encoding/comments/blanks before docstring.
    # Then allow a single module docstring (triple-quoted, optionally prefixed with r/u).
    # Then require: from __future__ import annotations
    i = 0
    while i < len(lines):
        s = lines[i].strip()
        if not s or s.startswith("#"):
            i += 1
            continue
        break

    assert i < len(lines), "file is empty"

    first = lines[i].lstrip()
    assert first.startswith(('"""', "r\"\"\"", "u\"\"\"", "ur\"\"\"", "ru\"\"\"", "'''", "r'''", "u'''", "ur'''", "ru'''")), (
        "Expected module docstring to be the first statement (after comments)."
    )

    quote = "\"\"\"" if "\"\"\"" in first else "'''"
    # If the docstring is one-line, it ends on the same line.
    if first.count(quote) >= 2:
        i += 1
    else:
        i += 1
        while i < len(lines):
            if quote in lines[i]:
                i += 1
                break
            i += 1

    remaining = _strip_leading_trivia(lines[i:])
    assert remaining, "expected content after module docstring"

    assert remaining[0].strip() == "from __future__ import annotations", (
        "`from __future__ import annotations` must be the first statement after the module docstring."
    )
