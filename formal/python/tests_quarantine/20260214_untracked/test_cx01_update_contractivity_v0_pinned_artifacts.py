from __future__ import annotations

from pathlib import Path

from formal.python.toe.comparators.cx01_update_contractivity_v0 import (
    _load_cx01_report_artifact,
    cx01_update_contractivity_v0_record,
)


def test_cx01_pinned_artifacts_exist_and_unblock() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    artifact_dir = repo_root / "formal" / "external_evidence" / "cx01_update_contractivity_domain_01"
    ref_path = artifact_dir / "cx01_reference_report.json"
    cand_path = artifact_dir / "cx01_candidate_report.json"

    assert ref_path.exists(), f"Missing CX-01 reference artifact: {ref_path}"
    assert cand_path.exists(), f"Missing CX-01 candidate artifact: {cand_path}"

    _, ref_ok = _load_cx01_report_artifact(ref_path)
    _, cand_ok = _load_cx01_report_artifact(cand_path)
    assert ref_ok is True
    assert cand_ok is True

    rec = cx01_update_contractivity_v0_record(date="2026-02-11", tolerance_profile="pinned")
    assert rec.status["blocked"] is False
    assert len(rec.rows) == 2
    limits = set(rec.scope_limits)
    assert "typed_artifacts_only" in limits
    assert "deterministic_record_only" in limits
