from __future__ import annotations

from pathlib import Path


def test_rl08_gauge_redundancy_lane_doc_exists_and_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/rl08_gauge_redundancy_invariance_lane_spec.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing RL08 spec doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "RL08",
        "gauge redundancy",
        "positive control",
        "negative control",
        "psi(x)",
        "exp(i*phi(x))",
        "alpha=0.2",
        "|psi(x)|^2",
        "eps_invariant=1e-10",
        "eps_break=1e-3",
        "L=6.283185307179586",
        "N=128",
    ]
    for required in required_strings:
        assert required in text, f"RL08 spec missing: {required}"
