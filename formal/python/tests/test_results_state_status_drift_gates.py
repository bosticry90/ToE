from __future__ import annotations

import re
from collections import Counter
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
RESULTS_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _results_rows(results_text: str) -> list[tuple[str, str]]:
    return re.findall(r"^\|\s*([A-Z0-9\-]+)\s*\|\s*`([^`]+)`\s*\|", results_text, flags=re.MULTILINE)


def _results_status_for(row_id: str, results_text: str) -> str:
    pattern = rf"^\|\s*{re.escape(row_id)}\s*\|\s*`([^`]+)`\s*\|"
    matches = re.findall(pattern, results_text, flags=re.MULTILINE)
    assert matches, f"Missing results row: {row_id}"
    assert len(matches) == 1, f"Expected exactly one results row for {row_id}, found {len(matches)}"
    return matches[0]


def _state_status_for(row_id: str, state_text: str) -> str:
    pattern = rf"`{re.escape(row_id)}:\s*([A-Z\-]+)`"
    matches = re.findall(pattern, state_text)
    assert matches, f"Missing state status token for {row_id}"
    assert len(matches) == 1, f"Expected exactly one state status token for {row_id}, found {len(matches)}"
    return matches[0]


def test_results_table_has_no_duplicate_theorem_or_full_rows() -> None:
    results_text = _read(RESULTS_PATH)
    row_ids = [row_id for row_id, _status in _results_rows(results_text)]

    theorem_and_full_ids = [
        row_id
        for row_id in row_ids
        if re.match(r"^TOE\-.*\-(THM|FULL)\-[A-Z0-9]+$", row_id)
    ]

    counts = Counter(theorem_and_full_ids)
    duplicates = {row_id: count for row_id, count in counts.items() if count > 1}
    assert not duplicates, (
        "Duplicate TOE-*-THM-* or TOE-*-FULL-* rows in RESULTS_TABLE_v0.md: "
        + ", ".join(f"{row_id} (x{count})" for row_id, count in sorted(duplicates.items()))
    )


def test_qm_theorem_row_is_singleton_and_not_legacy_conditional() -> None:
    results_text = _read(RESULTS_PATH)

    qm_rows = re.findall(r"^\|\s*TOE\-QM\-THM\-01\s*\|\s*`([^`]+)`\s*\|", results_text, flags=re.MULTILINE)
    assert len(qm_rows) == 1, (
        "TOE-QM-THM-01 must appear exactly once in RESULTS_TABLE_v0.md; "
        f"found {len(qm_rows)} occurrence(s)."
    )
    assert qm_rows[0] == "T-PROVED", (
        "TOE-QM-THM-01 must be T-PROVED and must not retain a legacy T-CONDITIONAL row; "
        f"found status {qm_rows[0]}."
    )

    assert "| TOE-QM-THM-01 | `T-CONDITIONAL` |" not in results_text, (
        "Legacy TOE-QM-THM-01 T-CONDITIONAL row must not exist in RESULTS_TABLE_v0.md."
    )


def test_selected_status_rows_match_between_state_and_results() -> None:
    state_text = _read(STATE_PATH)
    results_text = _read(RESULTS_PATH)

    status_carrying_ids = ("TOE-QM-THM-01", "TOE-GR-DER-01", "TOE-GR-DER-02")

    mismatches: list[str] = []
    for row_id in status_carrying_ids:
        state_status = _state_status_for(row_id, state_text)
        results_status = _results_status_for(row_id, results_text)
        if state_status != results_status:
            mismatches.append(f"{row_id}: state={state_status}, results={results_status}")

    assert not mismatches, "State/Results status drift detected: " + "; ".join(mismatches)
