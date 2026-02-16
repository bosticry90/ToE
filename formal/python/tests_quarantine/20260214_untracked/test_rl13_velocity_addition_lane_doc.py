from __future__ import annotations

from pathlib import Path


def test_rl13_velocity_addition_lane_doc_exists_and_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/rl13_velocity_addition_group_law_lane_spec.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing RL13 spec doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "RL13",
        "velocity",
        "addition",
        "Einstein",
        "Galilean",
        "positive control",
        "negative control",
        "c=1.0",
        "beta_u=0.3",
        "beta_v=0.4",
        "beta_uv = (beta_u + beta_v)/(1 + beta_u*beta_v)",
        "addition_residual",
        "eps_addition=1e-8",
        "eps_break=1e-3",
    ]
    for required in required_strings:
        assert required in text, f"RL13 spec missing: {required}"
