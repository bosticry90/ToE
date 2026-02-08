from __future__ import annotations

from pathlib import Path

from formal.python.toe.observables.ovdrbr01_candidate_pruning_table_record import (
    ovdrbr01_candidate_pruning_table_record,
)
from formal.python.toe.observables.ovdrbr01_lane_profile import (
    ovdrbr01_lane_profile_from_manifest,
)


REPO_ROOT = Path(__file__).resolve().parents[3]


def test_ov_dr_br01_elimination_exists_on_canonical_non_override_lane():
    """
    A2 lock: at least one candidate family is eliminated on the canonical (non-override) lane.
    """
    rec = ovdrbr01_candidate_pruning_table_record(date="2026-01-25")

    manifest_path = Path(str((rec.status or {}).get("admissibility_manifest", {}).get("path", "")))
    assert manifest_path.exists()

    lane = ovdrbr01_lane_profile_from_manifest(
        manifest_path,
        required_gate_ids=tuple((rec.status or {}).get("required_gates") or ("CT01", "SYM01", "CAUS01")),
    )
    assert lane.lane_kind == "canonical_disabled_default"
    assert lane.is_override is False

    false_rows = [r for r in rec.rows if str(r.get("survives_br01_constraints")) == "false"]
    assert len(false_rows) >= 1

    allowed_reason_atoms = {
        "declared_br05_structure_satisfied",
        "missing_required_br05_condition_keys",
        "missing_required_br05_fields",
        "no_formal_br05_prediction_declared",
    }

    for row in false_rows:
        reasons = list(row.get("reason_codes") or [])
        assert len(reasons) >= 1
        for reason in reasons:
            if str(reason).startswith("missing_keys:"):
                continue
            if str(reason).startswith("missing_fields:"):
                continue
            assert str(reason) in allowed_reason_atoms

    # Guard against pathological over-pruning: at least one declared survivor remains.
    counts = dict(rec.summary.get("counts") or {})
    assert int(counts.get("true", 0)) >= 1
