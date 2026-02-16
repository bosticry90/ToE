from __future__ import annotations

import json
from pathlib import Path

from formal.python.toe.comparators.ct08_external_anchor_dispersion_highk_slice_v0 import (
    _load_ct08_report_artifact,
    ct08_external_anchor_dispersion_highk_slice_v0_record,
)


def test_ct08_pinned_artifacts_exist_and_unblock() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    artifact_dir = repo_root / "formal" / "external_evidence" / "ct08_external_anchor_dispersion_highk_domain_01"
    ref_path = artifact_dir / "ct08_reference_report.json"
    cand_path = artifact_dir / "ct08_candidate_report.json"
    metadata_path = artifact_dir / "dataset_metadata.json"
    citation_path = artifact_dir / "source_citation.md"

    assert ref_path.exists(), f"Missing CT-08 reference artifact: {ref_path}"
    assert cand_path.exists(), f"Missing CT-08 candidate artifact: {cand_path}"
    assert metadata_path.exists(), f"Missing CT-08 dataset metadata: {metadata_path}"
    assert citation_path.exists(), f"Missing CT-08 source citation: {citation_path}"

    metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
    assert metadata.get("origin_dataset_id") == "Steinhauer2001_Fig3a_Digitized_v1"
    assert metadata.get("no_numeric_value_edits") is True
    transforms = list(metadata.get("transformations_performed", []))
    assert "filter k_um_inv >= quantile(k_um_inv, 0.5)" in transforms

    citation_text = citation_path.read_text(encoding="utf-8")
    assert "non_independent_of_CT06" in citation_text
    assert "Numeric edits: none." in citation_text

    _, ref_ok = _load_ct08_report_artifact(ref_path)
    _, cand_ok = _load_ct08_report_artifact(cand_path)
    assert ref_ok is True
    assert cand_ok is True

    rec = ct08_external_anchor_dispersion_highk_slice_v0_record(date="2026-02-10", tolerance_profile="pinned")
    assert rec.status["blocked"] is False
    assert len(rec.rows) == 2
    limits = set(rec.scope_limits)
    assert "typed_artifacts_only" in limits
    assert "deterministic_record_only" in limits
    assert "non_independent_of_CT06" in limits
