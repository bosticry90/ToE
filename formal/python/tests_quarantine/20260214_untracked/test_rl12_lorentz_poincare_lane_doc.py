from __future__ import annotations

from pathlib import Path


def test_rl12_lorentz_poincare_lane_doc_exists_and_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/rl12_lorentz_poincare_invariance_proxy_lane_spec.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing RL12 spec doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "RL12",
        "Lorentz",
        "Poincare",
        "positive control",
        "negative control",
        "boost",
        "x'",
        "t'",
        "gamma=1/sqrt(1-beta^2)",
        "c=1.0",
        "beta=0.3",
        "L=6.283185307179586",
        "T=3.141592653589793",
        "Nx=256",
        "Nt=128",
        "dx=L/Nx",
        "dt=T/Nt",
        "invariant_metric",
        "eps_invariant=1e-8",
        "eps_break=1e-3",
    ]
    for required in required_strings:
        assert required in text, f"RL12 spec missing: {required}"
