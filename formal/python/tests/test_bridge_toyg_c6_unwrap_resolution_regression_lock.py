from __future__ import annotations

import json
from pathlib import Path


def _repo_root_from_test_file(p: Path) -> Path:
    p = p.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def test_bridge_toyg_c6_unwrap_resolution_regression_lock() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    boundary_path = repo_root / "formal/quarantine/bridge_tickets/BRIDGE_TOYG_C6_unwrap_stability_BOUNDARY_REPORT.json"
    orth_path = repo_root / "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT.json"

    boundary = json.loads(boundary_path.read_text(encoding="utf-8"))
    orth = json.loads(orth_path.read_text(encoding="utf-8"))

    boundary_item = dict(boundary.get("items", [])[0])
    boundary_summary = dict(boundary_item.get("summary", {}))
    assert dict(boundary_summary.get("fail_reason_counts", {})) == {
        "fail_not_boundary_sensitive": 1,
        "fail_unwrap_step_mean_mismatch": 0,
        "fail_unwrap_step_variance_high": 1,
    }

    by_probe = {str(it.get("probe_id")): it for it in orth.get("items", [])}
    targeted = dict(by_probe["stress_toyg_unwrap"])
    assert str(targeted["toyg_winding"]["reason_code"]) == "fail_unwrap_discontinuity_guard"
    assert str(targeted["toyg_mode"]["reason_code"]) == "fail_peak_fraction_low"
    assert bool(targeted["toyg_unwrap"]["pass"]) is True
    assert str(targeted["toyg_unwrap"]["reason_code"]) == "pass_unwrap_stable_boundary"
    assert bool(targeted["toyg_bridge"]["pass"]) is True
    assert str(targeted["signature"]) == "P-P-P"
