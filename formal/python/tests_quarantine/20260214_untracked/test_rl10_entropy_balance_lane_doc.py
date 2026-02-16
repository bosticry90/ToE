from __future__ import annotations

from pathlib import Path


def test_rl10_entropy_balance_lane_doc_exists_and_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/rl10_entropy_balance_lane_spec.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing RL10 spec doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "RL10",
        "entropy production",
        "detailed balance",
        "positive control",
        "negative control",
        "N=3",
        "P_pos",
        "P_neg",
        "eps_balance=1e-8",
        "eps_entropy=1e-3",
        "row0: [0.7, 0.2, 0.1]",
        "row1: [0.2, 0.6, 0.2]",
        "row2: [0.1, 0.2, 0.7]",
        "row0: [0.7, 0.25, 0.05]",
        "row1: [0.05, 0.7, 0.25]",
        "row2: [0.25, 0.05, 0.7]",
    ]
    for required in required_strings:
        assert required in text, f"RL10 spec missing: {required}"
