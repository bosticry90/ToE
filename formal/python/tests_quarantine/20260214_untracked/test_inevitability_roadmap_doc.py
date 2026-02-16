from __future__ import annotations

from pathlib import Path


def test_inevitability_roadmap_doc_exists_and_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/programs/INEVITABILITY_ROADMAP_v0.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing inevitability roadmap doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "INEVITABILITY_ROADMAP_v0",
        "Scope and Intent",
        "Definitions",
        "Structural inevitability (conditional)",
        "Isomorphic up to representation",
        "Completed Preconditions",
        "RL01-RL16",
        "hard stop at RL16",
        "Program Phases",
        "Phase A",
        "External Anchors",
        "Phase B",
        "Conditional No-Go Theorems",
        "CT Program",
        "Phase C",
        "Universality and Robustness",
        "Phase D",
        "Representation Invariance",
        "Phase E",
        "Minimality Analysis",
        "Phase F",
        "Replication Readiness",
        "Explicit Non-Goals",
        "Governance and Revision",
        "doc-gate update",
        "governance-suite approval",
    ]
    for required in required_strings:
        assert required in text, f"Inevitability roadmap doc missing: {required}"
