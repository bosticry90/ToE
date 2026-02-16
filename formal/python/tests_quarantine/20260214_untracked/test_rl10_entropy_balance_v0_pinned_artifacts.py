from __future__ import annotations

from pathlib import Path

from formal.python.toe.comparators.rl10_entropy_balance_v0 import (
    _load_rl10_report_artifact,
    rl10_entropy_balance_v0_record,
)


def test_rl10_pinned_artifacts_exist_and_unblock() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    artifact_dir = repo_root / "formal" / "external_evidence" / "rl10_entropy_balance_domain_01"
    ref_path = artifact_dir / "rl10_reference_report.json"
    cand_path = artifact_dir / "rl10_candidate_report.json"

    assert ref_path.exists(), f"Missing RL10 reference artifact: {ref_path}"
    assert cand_path.exists(), f"Missing RL10 candidate artifact: {cand_path}"

    _, ref_ok = _load_rl10_report_artifact(ref_path)
    _, cand_ok = _load_rl10_report_artifact(cand_path)
    assert ref_ok is True
    assert cand_ok is True

    rec = rl10_entropy_balance_v0_record(date="2026-02-09", tolerance_profile="pinned")
    assert rec.status["blocked"] is False
    assert len(rec.rows) == 2
    limits = set(rec.scope_limits)
    assert "typed_artifacts_only" in limits
    assert "deterministic_record_only" in limits
