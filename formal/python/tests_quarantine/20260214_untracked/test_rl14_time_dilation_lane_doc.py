from __future__ import annotations

from pathlib import Path


def test_rl14_time_dilation_lane_doc_exists_and_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/rl14_time_dilation_proxy_lane_spec.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing RL14 spec doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "RL14",
        "time dilation",
        "positive control",
        "negative control",
        "c=1.0",
        "beta=0.6",
        "gamma=1/sqrt(1-beta^2)",
        "delta_t=2.0",
        "delta_tau",
        "dilation_residual",
        "eps_dilation=1e-8",
        "eps_break=1e-3",
    ]
    for required in required_strings:
        assert required in text, f"RL14 spec missing: {required}"
