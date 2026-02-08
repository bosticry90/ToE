from __future__ import annotations

from pathlib import Path

from formal.python.toe.observables.ovdrbr01_candidate_pruning_table_record import (
    ovdrbr01_candidate_pruning_table_record,
)


REPO_ROOT = Path(__file__).resolve().parents[3]


def test_ov_dr_br01_elimination_exists_on_canonical_non_override_lane():
    """
    A2 lock: at least one candidate family is eliminated on the canonical (non-override) lane.
    """
    rec = ovdrbr01_candidate_pruning_table_record(date="2026-01-25")

    manifest_path = str((rec.status or {}).get("admissibility_manifest", {}).get("path", ""))
    assert "ENABLED_OVERRIDE" not in manifest_path

    br05_path = str((rec.inputs or {}).get("OV-BR-05", {}).get("path", ""))
    pred_path = str((rec.inputs or {}).get("OV-DR-BR-00", {}).get("path", ""))
    assert "OVERRIDE" not in br05_path.upper()
    assert "OVERRIDE" not in pred_path.upper()

    false_rows = [r for r in rec.rows if str(r.get("survives_br01_constraints")) == "false"]
    assert len(false_rows) >= 1
    for row in false_rows:
        reasons = list(row.get("reason_codes") or [])
        assert len(reasons) >= 1
