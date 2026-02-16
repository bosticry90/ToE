from __future__ import annotations

from pathlib import Path


def test_ct06_external_anchor_dispersion_lane_doc_exists_and_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/programs/CT06_external_anchor_dispersion_v0.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing CT-06 spec doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "CT-06",
        "Status: Pinned (v0)",
        "external anchor",
        "dispersion",
        "Steinhauer2001_Fig3a_Digitized_v1",
        "preprocessing assumptions",
        "omega_over_2pi_kHz_vs_k_um_inv",
        "positive control",
        "negative control",
        "eps_rmse_kHz",
        "eps_max_abs_error_kHz",
        "eps_reduced_chi2",
    ]
    for required in required_strings:
        assert required in text, f"CT-06 spec missing: {required}"
