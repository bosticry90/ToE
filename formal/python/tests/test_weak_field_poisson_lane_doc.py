from __future__ import annotations

from pathlib import Path


def test_weak_field_poisson_lane_doc_exists() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/quarantine/physics_target/RL03_weak_field_poisson_v0_SPEC.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing lane spec doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "COMP-RL-03/v0",
        "weak-field",
        "Poisson",
        "nabla^2 Phi = kappa * rho",
        "representation-eligible",
        "factor-through `.val`",
    ]
    for required in required_strings:
        assert required in text, f"Lane spec doc missing: {required}"
