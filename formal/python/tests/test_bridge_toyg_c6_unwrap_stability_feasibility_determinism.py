from __future__ import annotations

from pathlib import Path

from formal.python.tools.bridge_toyg_c6_unwrap_stability_feasibility import (
    build_bridge_toyg_c6_unwrap_stability_feasibility,
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


def test_bridge_toyg_c6_unwrap_stability_feasibility_is_deterministic() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    p1 = build_bridge_toyg_c6_unwrap_stability_feasibility(repo_root=repo_root)
    p2 = build_bridge_toyg_c6_unwrap_stability_feasibility(repo_root=repo_root)

    assert p1 == p2
    assert p1.get("schema_version") == 1
    assert p1.get("bridge_id") == "BRIDGE_TICKET_TOYG_0003"
    assert p1.get("mode") == "design_only_preimplementation"
    assert p1.get("selected_target_reason_code") == "mismatch_toyg_bridge_only"
    assert p1.get("implementable") is True
    assert p1.get("found") is True

    checks = dict(p1.get("checks", {}))
    assert checks.get("selected_target_present") is True
    assert int(checks.get("selected_target_resolved_by_unwrap_count", 0)) >= 1

    target = dict(p1.get("target_region", {}))
    assert int(target.get("count", 0)) >= 0
    assert int(target.get("resolved_by_unwrap_count", 0)) >= 1
    assert list(target.get("probe_ids", [])) == ["stress_toyg_unwrap"]
