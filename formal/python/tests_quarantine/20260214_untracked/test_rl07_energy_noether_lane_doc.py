from __future__ import annotations

from pathlib import Path


def test_rl07_energy_noether_lane_doc_exists_and_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/rl07_energy_noether_conservation_lane_spec.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing RL07 spec doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "RL07",
        "energy conservation",
        "Stormer-Verlet",
        "leapfrog",
        "negative control",
        "relative energy drift",
        "energy drop",
        "N=128",
        "L=6.283185307179586",
        "c=1.0",
        "dt=0.1*dx",
        "steps=2000",
        "gamma=0.02",
        "eps_drift=5e-3",
        "eps_drop=0.10",
    ]
    for required in required_strings:
        assert required in text, f"RL07 spec missing: {required}"
