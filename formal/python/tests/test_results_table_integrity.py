from __future__ import annotations

import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
RESULTS_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_rows(results_text: str) -> list[dict[str, str]]:
    """
    Extract markdown table rows of the form:
      | ROW_ID | `STATUS` | DESCRIPTION | ...
    """
    rows: list[dict[str, str]] = []
    for m in re.finditer(
        r"^\|\s*([^|]+?)\s*\|\s*`([^`]+)`\s*\|\s*([^|]+?)\s*\|",
        results_text,
        flags=re.MULTILINE,
    ):
        row_id = m.group(1).strip()
        status = m.group(2).strip()
        desc = m.group(3).strip()
        rows.append({"row_id": row_id, "status": status, "desc": desc})
    assert rows, "No rows parsed from RESULTS_TABLE_v0.md; table format may have changed."
    return rows


def test_results_table_row_ids_are_unique() -> None:
    text = _read(RESULTS_PATH)
    rows = _extract_rows(text)
    ids = [r["row_id"] for r in rows]
    duplicates = sorted({row_id for row_id in ids if ids.count(row_id) > 1})
    assert not duplicates, "Duplicate row_id(s) found in RESULTS_TABLE_v0.md:\n- " + "\n- ".join(duplicates)


def test_results_table_status_values_are_well_formed() -> None:
    text = _read(RESULTS_PATH)
    rows = _extract_rows(text)

    allowed_prefixes = ("T-", "B-", "P-", "E-")
    violations: list[str] = []
    for row in rows:
        status = row["status"]
        if not status.startswith(allowed_prefixes):
            violations.append(
                f"{row['row_id']}: unexpected status `{status}` (expected one of {allowed_prefixes})"
            )

    assert not violations, "Status formatting violations:\n- " + "\n- ".join(violations)
