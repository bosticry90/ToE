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
    We only care about row_id, status, and description.
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


def _row_class(row_id: str) -> str | None:
    """
    Minimal row class heuristic:
      - DER rows: contain '-DER-' (governance/closure coupling rows)
      - THM rows: contain '-THM-' (theorem-closure claim rows)
      - FULL rows: contain '-FULL-' (theorem-grade full package rows)
    """
    if "-DER-" in row_id:
        return "DER"
    if "-THM-" in row_id:
        return "THM"
    if "-FULL-" in row_id:
        return "FULL"
    return None


def _is_blocked(status: str) -> bool:
    return status.startswith("B-")


def test_results_row_class_semantics_policy_v0() -> None:
    """
    Policy:
      - DER rows are governance/closure-coupling rows.
        * Non-blocked DER rows may be T-CONDITIONAL (or other explicitly governance labels),
          but must not be T-PROVED (to prevent theorem-closure confusion).
        * DER row descriptions should include at least one governance cue and at least one
          non-theorem cue.
      - THM/FULL rows are theorem-closure claim rows.
        * If non-blocked, status should be theorem-grade, not T-CONDITIONAL.
    """
    text = _read(RESULTS_PATH)
    rows = _extract_rows(text)

    # Allowed status sets (keep intentionally small and explicit).
    allowed_nonblocked_der = {"T-CONDITIONAL", "P-POLICY"}
    forbidden_der = {"T-PROVED"}

    # For theorem rows: allow blocked, or theorem-grade when non-blocked.
    allowed_nonblocked_theorem = {"T-PROVED"}

    # Lightweight cues to prevent drift; keep permissive to avoid brittle phrasing gates.
    governance_cues = [
        "Governance",
        "governance",
        "gate",
        "closure",
        "roadmap",
        "coupling",
        "bounded",
        "adjudication",
        "synchronized",
    ]
    non_theorem_cues = [
        "Not a theorem",
        "not a theorem",
        "not theorem-level",
        "not a theorem-level",
        "governance scope only",
        "Governance scope only",
        "theorem-conditional",
    ]

    failures: list[str] = []

    for r in rows:
        row_id = r["row_id"]
        status = r["status"]
        desc = r["desc"]
        cls = _row_class(row_id)
        if cls is None:
            continue

        if cls == "DER":
            if status in forbidden_der:
                failures.append(
                    f"{row_id}: DER row must not use theorem-grade status `{status}`."
                )
            if not _is_blocked(status) and status not in allowed_nonblocked_der:
                failures.append(
                    f"{row_id}: DER non-blocked status `{status}` not allowed; "
                    f"expected one of {sorted(allowed_nonblocked_der)}."
                )

            # Only enforce narrative cues when non-blocked (post-discharge clarity).
            if not _is_blocked(status):
                if not any(cue in desc for cue in governance_cues):
                    failures.append(
                        f"{row_id}: DER row description missing governance/closure cue "
                        f"(expected one of {governance_cues})."
                    )
                if not any(cue in desc for cue in non_theorem_cues):
                    failures.append(
                        f"{row_id}: DER row description missing non-theorem cue "
                        f"(expected one of {non_theorem_cues})."
                    )

        if cls in {"THM", "FULL"}:
            if not _is_blocked(status) and status not in allowed_nonblocked_theorem:
                failures.append(
                    f"{row_id}: {cls} row is non-blocked with `{status}`; expected theorem-grade "
                    f"status {sorted(allowed_nonblocked_theorem)}."
                )
            if status == "T-CONDITIONAL":
                failures.append(
                    f"{row_id}: {cls} row must not use `T-CONDITIONAL` (reserve for DER rows)."
                )

    assert not failures, "Row-class semantics policy violations:\n- " + "\n- ".join(failures)
