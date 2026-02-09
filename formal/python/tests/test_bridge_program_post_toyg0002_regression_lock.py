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


def test_bridge_program_post_toyg0002_regression_lock() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    orth_path = repo_root / "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT.json"
    mismatch_path = repo_root / "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json"

    orth = json.loads(orth_path.read_text(encoding="utf-8"))
    mismatch = json.loads(mismatch_path.read_text(encoding="utf-8"))

    orth_summary = dict(orth.get("summary", {}))
    resolution = dict(orth_summary.get("targeted_resolution", {}))
    mismatch_summary = dict(mismatch.get("summary", {}))

    assert orth_summary.get("nonredundant") is True
    assert int(resolution.get("n_winding_not_integer_close_resolved_by_mode", 0)) == 1
    assert int(resolution.get("n_winding_unwrap_guard_resolved_by_unwrap", 0)) == 1
    assert int(resolution.get("n_phase_control_fail_resolved_by_phase_anchor", 0)) == 1
    assert int(resolution.get("n_current_control_fail_resolved_by_current_anchor", 0)) == 1
    assert int(resolution.get("n_pair_vs_bridge_resolved_by_pair_channel", 0)) >= 1

    assert int(mismatch_summary.get("n_mismatch", 0)) == 0
    assert dict(mismatch_summary.get("reason_code_counts", {})) == {}
