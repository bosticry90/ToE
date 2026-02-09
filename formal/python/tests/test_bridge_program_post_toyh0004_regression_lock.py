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


def test_bridge_program_post_toyh0004_regression_lock() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    orth_path = repo_root / "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT.json"
    orth = json.loads(orth_path.read_text(encoding="utf-8"))

    orth_summary = dict(orth.get("summary", {}))
    resolution = dict(orth_summary.get("targeted_resolution", {}))

    assert orth_summary.get("nonredundant") is True
    assert int(resolution.get("n_current_control_fail_resolved_by_current_anchor", 0)) >= 1

