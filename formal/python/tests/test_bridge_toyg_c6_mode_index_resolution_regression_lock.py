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


def test_bridge_toyg_c6_mode_index_boundary_and_resolution_lock() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    boundary_path = repo_root / "formal/quarantine/bridge_tickets/BRIDGE_TOYG_C6_mode_index_BOUNDARY_REPORT.json"
    orth_path = repo_root / "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT.json"

    boundary = json.loads(boundary_path.read_text(encoding="utf-8"))
    orth = json.loads(orth_path.read_text(encoding="utf-8"))

    boundary_item = dict(boundary.get("items", [])[0])
    boundary_summary = dict(boundary_item.get("summary", {}))

    assert int(boundary_summary.get("n_samples", 0)) == 4
    assert int(boundary_summary.get("n_pass", 0)) == 2
    assert int(boundary_summary.get("n_fail", 0)) == 2
    assert dict(boundary_summary.get("fail_reason_counts", {})) == {
        "fail_mode_index_mismatch": 0,
        "fail_not_integer_close": 1,
        "fail_peak_fraction_low": 1,
    }

    by_probe = {str(it.get("probe_id")): it for it in orth.get("items", [])}
    targeted = dict(by_probe["stress_toyg_integer"])

    assert str(targeted["toyg_winding"]["reason_code"]) == "fail_not_integer_close"
    assert bool(targeted["toyg_mode"]["pass"]) is True
    assert str(targeted["toyg_mode"]["reason_code"]) == "pass_mode_index_1"
    assert bool(targeted["toyg_bridge"]["pass"]) is True
    assert str(targeted["signature"]) == "P-P-P"
