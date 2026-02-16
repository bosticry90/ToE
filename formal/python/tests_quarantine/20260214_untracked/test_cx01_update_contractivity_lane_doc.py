from __future__ import annotations

from pathlib import Path


def test_cx01_update_contractivity_lane_doc_exists_and_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/programs/CX01_update_contractivity_lane_spec.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing CX-01 spec doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "CX-01",
        "contractive",
        "positive control",
        "negative control",
        "k_contract=0.8",
        "k_break=1.05",
        "empirical_lipschitz",
        "eps_contractivity=1e-8",
        "eps_break=1e-3",
    ]
    for required in required_strings:
        assert required in text, f"CX-01 spec missing: {required}"
