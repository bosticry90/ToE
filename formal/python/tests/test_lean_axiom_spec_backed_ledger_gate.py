from __future__ import annotations

import re
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
)


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_ROOT = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal"
LEDGER_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md"

ALLOWED_STATUSES = {
    "live_blocking",
    "live_nonblocking",
    "retained_assumption",
    "historical",
    "quarantine",
    "spec_backed",
    "candidate_for_removal",
}
REQUIRED_FIELDS = [
    "declaration",
    "file",
    "status",
    "reason",
    "associated_pillar_or_seam",
    "blocks_full_pillar_target",
    "replacement_or_discharge_path",
]
AXIOM_RE = re.compile(r"^\s*axiom\s+([A-Za-z_][A-Za-z0-9_'.]*)\b", re.MULTILINE)
SORRY_OR_ADMIT_RE = re.compile(r"\b(?:sorry|admit)\b")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _strip_lean_comments(text: str) -> str:
    result: list[str] = []
    i = 0
    depth = 0
    while i < len(text):
        if depth == 0 and text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                result.append(" ")
                i += 1
            continue
        if text.startswith("/-", i):
            depth += 1
            result.extend("  ")
            i += 2
            continue
        if depth > 0:
            if text.startswith("-/", i):
                depth -= 1
                result.extend("  ")
                i += 2
                continue
            result.append("\n" if text[i] == "\n" else " ")
            i += 1
            continue
        result.append(text[i])
        i += 1
    return "".join(result)


def _lean_surface_debt() -> tuple[list[tuple[str, str]], list[tuple[str, str]]]:
    axioms: list[tuple[str, str]] = []
    sorry_or_admit: list[tuple[str, str]] = []
    for path in sorted(LEAN_ROOT.rglob("*.lean")):
        rel = str(path.relative_to(REPO_ROOT)).replace("\\", "/")
        uncommented = _strip_lean_comments(_read(path))
        for match in AXIOM_RE.finditer(uncommented):
            axioms.append((match.group(1), rel))
        for match in SORRY_OR_ADMIT_RE.finditer(uncommented):
            sorry_or_admit.append((match.group(0), rel))
    return axioms, sorry_or_admit


def _unquote_cell(cell: str) -> str:
    value = cell.strip()
    if value.startswith("`") and value.endswith("`"):
        return value[1:-1]
    return value


def _ledger_rows() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    headers: list[str] = []
    in_table = False
    for line in _read(LEDGER_PATH).splitlines():
        if line.startswith("| declaration |"):
            in_table = True
            headers = [part.strip() for part in line.strip("|").split("|")]
            continue
        if not in_table:
            continue
        if line.startswith("| ---"):
            continue
        if not line.startswith("|"):
            break
        cells = [_unquote_cell(part) for part in line.strip("|").split("|")]
        assert len(cells) == len(headers), line
        rows.append(dict(zip(headers, cells, strict=True)))
    assert rows, "Ledger rows table was not parsed."
    return rows


def test_ledger_baseline_matches_real_uncommented_lean_debt() -> None:
    text = _read(LEDGER_PATH)
    axioms, sorry_or_admit = _lean_surface_debt()

    assert f"real_axiom_count_v0: {len(axioms)}" in text
    assert f"real_sorry_or_admit_count_v0: {len(sorry_or_admit)}" in text
    assert f"real_axiom_file_count_v0: {len({file for _, file in axioms})}" in text
    assert len(axioms) == 60
    assert len(sorry_or_admit) == 0


def test_every_real_axiom_has_a_ledger_row() -> None:
    axioms, _ = _lean_surface_debt()
    rows = _ledger_rows()
    ledger_pairs = {(row["declaration"], row["file"]) for row in rows}

    missing = sorted(set(axioms) - ledger_pairs)
    extra = sorted(ledger_pairs - set(axioms))
    assert not missing, "Axiom(s) missing from ledger: " + repr(missing)
    assert not extra, "Ledger row(s) do not match real uncommented axioms: " + repr(extra)


def test_ledger_rows_have_required_fields_and_allowed_statuses() -> None:
    rows = _ledger_rows()
    assert len(rows) == 60

    for row in rows:
        assert set(row) == set(REQUIRED_FIELDS)
        for field in REQUIRED_FIELDS:
            assert row[field], row
        assert row["status"] in ALLOWED_STATUSES, row
        assert row["blocks_full_pillar_target"] in {"yes", "no"}, row
        if row["blocks_full_pillar_target"] == "yes":
            assert row["status"] in {
                "live_blocking",
                "retained_assumption",
                "quarantine",
                "candidate_for_removal",
            }, row


def test_ledger_gate_is_not_governance_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled("test_lean_axiom_spec_backed_ledger_gate.py")
