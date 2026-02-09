from __future__ import annotations

from pathlib import Path

from formal.python.tools.bridge_toyh_c6_current_invariance_feasibility import (
    build_bridge_toyh_c6_current_invariance_feasibility,
)


def _repo_root_from_test_file(p: Path) -> Path:
    p = p.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def test_bridge_toyh_c6_current_invariance_feasibility_is_deterministic() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    p1 = build_bridge_toyh_c6_current_invariance_feasibility(repo_root=repo_root)
    p2 = build_bridge_toyh_c6_current_invariance_feasibility(repo_root=repo_root)

    assert p1 == p2
    assert p1.get("schema_version") == 1
    assert p1.get("bridge_id") == "BRIDGE_TICKET_TOYH_0002"
    assert p1.get("found") is True
