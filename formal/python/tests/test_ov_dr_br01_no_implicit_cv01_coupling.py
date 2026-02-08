from __future__ import annotations

import ast
from pathlib import Path

from formal.python.toe.observables.ovcvbr01_cv01_v1_pruning_bridge_record import (
    ovcvbr01_cv01_v1_pruning_bridge_record,
)
from formal.python.toe.observables.ovdrbr01_candidate_pruning_table_record import (
    ovdrbr01_candidate_pruning_table_record,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
OVDR_FILE = REPO_ROOT / "formal" / "python" / "toe" / "observables" / "ovdrbr01_candidate_pruning_table_record.py"


def _imported_modules(path: Path) -> set[str]:
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    mods: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for n in node.names:
                mods.add(str(n.name))
        elif isinstance(node, ast.ImportFrom):
            if node.module:
                mods.add(str(node.module))
    return mods


def test_ov_dr_br01_source_has_no_cv01_or_bridge_imports():
    mods = _imported_modules(OVDR_FILE)
    banned_fragments = ("cv01", "ovcvbr01")
    offenders = sorted([m for m in mods if any(frag in m.lower() for frag in banned_fragments)])
    assert not offenders, f"Found implicit CV01 coupling imports in OV-DR-BR-01 source: {offenders}"


def test_ov_dr_br01_record_is_unchanged_by_running_cv01_bridge_lane():
    base_before = ovdrbr01_candidate_pruning_table_record(date="2026-01-25").to_jsonable()

    fixture = REPO_ROOT / "formal" / "external_evidence" / "cv01_v1_negative_control_fixture"
    _ = ovcvbr01_cv01_v1_pruning_bridge_record(
        date="2026-02-08",
        cv01_tolerance_profile="pinned",
        cv01_artifact_dir=fixture,
    )

    base_after = ovdrbr01_candidate_pruning_table_record(date="2026-01-25").to_jsonable()
    assert base_before == base_after

    for row in list(base_after.get("rows") or []):
        for code in list(row.get("reason_codes") or []):
            assert "cv01" not in str(code).lower()
