from __future__ import annotations

from pathlib import Path

from formal.python.toe.comparators.ct05_rep_invariant_admissibility_class_v0 import (
    _load_ct05_report_artifact,
    ct05_rep_invariant_admissibility_class_v0_record,
)


def test_ct05_pinned_artifacts_exist_and_unblock() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    artifact_dir = repo_root / "formal" / "external_evidence" / "ct05_rep_invariant_admissibility_class_domain_01"
    ref_path = artifact_dir / "ct05_reference_report.json"
    cand_path = artifact_dir / "ct05_candidate_report.json"

    assert ref_path.exists(), f"Missing CT-05 reference artifact: {ref_path}"
    assert cand_path.exists(), f"Missing CT-05 candidate artifact: {cand_path}"

    _, ref_ok = _load_ct05_report_artifact(ref_path)
    _, cand_ok = _load_ct05_report_artifact(cand_path)
    assert ref_ok is True
    assert cand_ok is True

    rec = ct05_rep_invariant_admissibility_class_v0_record(date="2026-02-09", tolerance_profile="pinned")
    assert rec.status["blocked"] is False
    assert len(rec.rows) == 3
    limits = set(rec.scope_limits)
    assert "typed_artifacts_only" in limits
    assert "deterministic_record_only" in limits
