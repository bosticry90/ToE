from __future__ import annotations

from pathlib import Path

from formal.python.tools.bridge_toyg_canonical_feasibility_scan import (
    scan_bridge_toyg_canonical_feasibility,
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


def test_bridge_toyg_canonical_feasibility_scan_is_deterministic() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    p1 = scan_bridge_toyg_canonical_feasibility(repo_root=repo_root)
    p2 = scan_bridge_toyg_canonical_feasibility(repo_root=repo_root)

    assert p1 == p2
    assert p1.get("schema_version") == 1
    assert p1.get("bridge_family") == "BRIDGE_TOYG_CANONICAL_FEASIBILITY"
    assert p1.get("toy_family") == "TOY-G"
    assert p1.get("found") is True

    targets = {str(t.get("target_id")): t for t in p1.get("targets", [])}
    assert set(targets.keys()) == {"C6", "C7", "UCFF"}
    assert targets["C6"]["found"] is True
    assert targets["C7"]["found"] is False
    assert targets["UCFF"]["found"] is False
