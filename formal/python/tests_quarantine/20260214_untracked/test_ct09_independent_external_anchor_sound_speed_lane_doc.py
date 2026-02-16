from __future__ import annotations

from pathlib import Path


def test_ct09_independent_external_anchor_sound_speed_lane_doc_exists_and_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/programs/CT09_independent_external_anchor_sound_speed_v0.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing CT-09 spec doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "CT-09",
        "independent external anchor",
        "distance_um_vs_time_ms",
        "Andrews1997_Fig2_DistanceTime_Digitized_v1",
        "positive control",
        "negative control",
        "eps_rmse_um",
        "eps_max_abs_error_um",
        "eps_reduced_chi2",
        "semantically binding",
        "external_anchor_only",
    ]
    for required in required_strings:
        assert required in text, f"CT-09 spec missing: {required}"
