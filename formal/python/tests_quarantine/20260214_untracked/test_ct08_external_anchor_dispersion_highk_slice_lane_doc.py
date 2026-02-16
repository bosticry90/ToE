from __future__ import annotations

from pathlib import Path


def test_ct08_external_anchor_dispersion_highk_slice_lane_doc_exists_and_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/programs/CT08_external_anchor_dispersion_highk_slice_v0.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing CT-08 spec doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "CT-08",
        "external anchor",
        "dispersion",
        "Steinhauer2001_Fig3a_Digitized_v1",
        "high-k slice",
        "k_um_inv",
        "k_min_um_inv",
        "positive control",
        "negative control",
        "eps_rmse_kHz",
        "eps_max_abs_error_kHz",
        "eps_reduced_chi2",
        "non_independent_of_CT06",
    ]
    for required in required_strings:
        assert required in text, f"CT-08 spec missing: {required}"
