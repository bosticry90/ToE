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


def test_bridge_frontier_closure_regression_lock() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    orth_path = repo_root / "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT.json"
    mismatch_path = repo_root / "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json"
    summary_path = repo_root / "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_MISMATCH_REASON_SUMMARY.json"

    orth = json.loads(orth_path.read_text(encoding="utf-8"))
    mismatch = json.loads(mismatch_path.read_text(encoding="utf-8"))
    summary = json.loads(summary_path.read_text(encoding="utf-8"))

    orth_summary = dict(orth.get("summary", {}))
    mismatch_summary = dict(mismatch.get("summary", {}))
    reason_summary = dict(summary.get("summary", {}))
    recommended = dict(summary.get("recommended_next_target", {}))

    assert orth_summary.get("nonredundant") is True
    assert int(mismatch_summary.get("n_mismatch", 0)) == 0
    assert dict(mismatch_summary.get("reason_code_counts", {})) == {}
    assert int(reason_summary.get("n_mismatch", 0)) == 0
    assert dict(reason_summary.get("reason_code_counts", {})) == {}
    assert recommended.get("reason_code") == "none"
    assert recommended.get("suggested_design_ticket") == "BRIDGE_TICKET_PROGRAM_COMPLETE"

