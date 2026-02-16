from __future__ import annotations

from pathlib import Path


def test_rl11_causality_signal_cone_lane_doc_exists_and_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/rl11_causality_signal_cone_lane_spec.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing RL11 spec doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "RL11",
        "causality",
        "signal-cone",
        "domain-of-dependence",
        "positive control",
        "negative control",
        "L=6.283185307179586",
        "N=256",
        "dx=L/N",
        "c0=1.0",
        "CFL_max=1.0",
        "dt_pos=0.01",
        "dt_neg=0.05",
        "leakage_outside_cone",
        "eps_causal=1e-10",
        "eps_acausal=1e-3",
    ]
    for required in required_strings:
        assert required in text, f"RL11 spec missing: {required}"
