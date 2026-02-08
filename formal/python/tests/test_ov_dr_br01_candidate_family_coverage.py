from __future__ import annotations

import ast
from pathlib import Path

from formal.python.toe.observables.ovdrbr01_candidate_pruning_table_record import (
    ovdrbr01_candidate_pruning_table_record,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
CANDIDATE_FILE = REPO_ROOT / "formal" / "python" / "toe" / "bridges" / "br01_candidates.py"


def _candidate_ids_from_source() -> set[str]:
    tree = ast.parse(CANDIDATE_FILE.read_text(encoding="utf-8"), filename=str(CANDIDATE_FILE))
    out: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef) and node.name.startswith("BR01_"):
            out.add(node.name)
    return out


def test_ov_dr_br01_candidate_rows_cover_all_br01_families():
    rec = ovdrbr01_candidate_pruning_table_record(date="2026-01-25")
    rows = list(rec.rows)
    assert rows, "Expected explicit candidate rows in OV-DR-BR-01 pruning table"

    row_ids = {str(r["candidate_id"]) for r in rows}
    source_ids = _candidate_ids_from_source()
    assert row_ids == source_ids

    allowed = {"true", "false", "unknown"}
    for r in rows:
        assert str(r.get("survives_br01_constraints")) in allowed
        assert isinstance(r.get("reason_codes"), list)
        assert len(r.get("reason_codes")) >= 1


def test_ov_dr_br01_has_active_eliminator_and_survivor_statuses():
    rec = ovdrbr01_candidate_pruning_table_record(date="2026-01-25")
    counts = dict(rec.summary["counts"])

    # At least one candidate is structurally eliminated and at least one survives.
    assert int(counts["false"]) >= 1
    assert int(counts["true"]) >= 1

    total = int(counts["true"]) + int(counts["false"]) + int(counts["unknown"])
    assert total == len(rec.rows)
