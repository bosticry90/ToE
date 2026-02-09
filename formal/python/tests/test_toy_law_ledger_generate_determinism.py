from __future__ import annotations

from pathlib import Path

from formal.python.tools.toy_law_ledger_generate import SCHEMA_ID, build_toy_law_ledger_payload


def _repo_root_from_test_file(p: Path) -> Path:
    p = p.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def test_toy_law_ledger_is_deterministic() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    p1 = build_toy_law_ledger_payload(repo_root=repo_root)
    p2 = build_toy_law_ledger_payload(repo_root=repo_root)

    assert p1 == p2
    assert p1.get("schema") == SCHEMA_ID
    assert isinstance(p1.get("fingerprint"), str) and len(p1["fingerprint"]) == 64

    items = list(p1.get("items", []))
    assert len(items) == 11
    ids = {item.get("toy_law_id") for item in items}
    assert ids == {
        "TOY-A1-viability-gradient-step",
        "TOY-B1-coherence-transport",
        "TOY-B2-coherence-transport-proxy",
        "TOY-C1-metric-closure",
        "TOY-C2-metric-closure-curvature-proxy",
        "TOY-D1-regime-switching",
        "TOY-E1-scale-flow",
        "TOY-F1-stochastic-selection",
        "TOY-G1-topological-invariants",
        "TOY-H1-gauge-redundancy",
        "TOY-H2-gauge-redundancy-local",
    }
