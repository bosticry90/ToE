from __future__ import annotations

from pathlib import Path


def test_rl09_dispersion_topology_lane_doc_exists_and_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/rl09_dispersion_topology_bridge_lane_spec.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing RL09 spec doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "RL09",
        "dispersion",
        "topology",
        "winding",
        "positive control",
        "negative control",
        "H(k)",
        "sigma_x",
        "sigma_y",
        "t1=0.5",
        "t2=1.0",
        "t1=1.0",
        "t2=0.5",
        "N_k=256",
        "L=6.283185307179586",
        "eps_winding=1e-8",
    ]
    for required in required_strings:
        assert required in text, f"RL09 spec missing: {required}"
