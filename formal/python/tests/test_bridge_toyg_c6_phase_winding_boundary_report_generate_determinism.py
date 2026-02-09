from __future__ import annotations

from pathlib import Path

from formal.python.tools.bridge_toyg_c6_phase_winding_boundary_report_generate import (
    build_bridge_toyg_c6_phase_winding_boundary_report,
)


def test_bridge_toyg_c6_phase_winding_boundary_report_is_deterministic() -> None:
    repo_root = Path(__file__).resolve()
    while repo_root != repo_root.parent and not (repo_root / "formal").exists():
        repo_root = repo_root.parent
    assert (repo_root / "formal").exists()

    r1 = build_bridge_toyg_c6_phase_winding_boundary_report(repo_root=repo_root)
    r2 = build_bridge_toyg_c6_phase_winding_boundary_report(repo_root=repo_root)

    assert r1 == r2
    assert r1.get("schema_version") == 1
    items = list(r1.get("items", []))
    assert [it.get("ticket_id") for it in items] == ["BRIDGE_TICKET_TOYG_0001"]
    summary = dict(items[0].get("summary", {}))
    fail_reasons = dict(summary.get("fail_reason_counts", {}))
    assert fail_reasons.get("fail_not_integer_close", 0) >= 1
    assert fail_reasons.get("fail_unwrap_discontinuity_guard", 0) >= 1
    assert isinstance(r1.get("artifact_sha256"), str) and len(r1["artifact_sha256"]) == 64
