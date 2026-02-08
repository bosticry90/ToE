from __future__ import annotations

from pathlib import Path

from formal.python.toe.observables.ovcvbr01_cv01_v1_pruning_bridge_record import (
    ovcvbr01_cv01_v1_pruning_bridge_record,
)


REPO_ROOT = Path(__file__).resolve().parents[3]


def test_ov_cv_br01_elimination_is_attributable_to_cv01_reason_atom_without_override_lane() -> None:
    fixture = REPO_ROOT / "formal" / "external_evidence" / "cv01_v1_negative_control_fixture"

    rec = ovcvbr01_cv01_v1_pruning_bridge_record(
        date="2026-02-08",
        cv01_tolerance_profile="pinned",
        cv01_artifact_dir=fixture,
    )

    # OV-DR-BR-01 can be gate-blocked-by-default while still emitting a structural
    # pruning surface; this bridge consumes that surface deterministically.
    assert isinstance(rec.status["blocked"], bool)
    assert "missing_cv01_pruning_reason_policy" not in list(rec.status.get("reasons") or [])

    assert "cv01_fail_linear_vs_curved_speed_inconsistent" in rec.active_reason_codes
    assert "cv01_cross_artifact_inconsistent" in rec.active_reason_atoms

    rows = list(rec.rows)
    attributed = [r for r in rows if bool(r.get("cv01_attributed_elimination"))]
    assert len(attributed) >= 1

    # Guard against pathological over-pruning.
    counts = dict(rec.summary.get("counts") or {})
    assert int(counts.get("true", 0)) >= 1

    # At least one elimination reason must explicitly reference the CV01 reason atom.
    has_atom_reason = False
    for row in attributed:
        for code in list(row.get("reason_codes") or []):
            if str(code).startswith("eliminated_by_cv01_reason_atom:"):
                has_atom_reason = True
                break
        if has_atom_reason:
            break
    assert has_atom_reason
