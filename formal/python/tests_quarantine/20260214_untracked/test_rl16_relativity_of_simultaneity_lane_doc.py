from __future__ import annotations

from pathlib import Path


def test_rl16_relativity_of_simultaneity_lane_doc_exists_and_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/rl16_relativity_of_simultaneity_proxy_lane_spec.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing RL16 spec doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "RL16",
        "simultaneity",
        "positive control",
        "negative control",
        "c=1.0",
        "beta=0.6",
        "gamma=1/sqrt(1-beta^2)",
        "delta_t=0.2",
        "delta_x=1.5",
        "delta_t_prime",
        "simultaneity_residual",
        "eps_simultaneity=1e-8",
        "eps_break=1e-3",
    ]
    for required in required_strings:
        assert required in text, f"RL16 spec missing: {required}"
