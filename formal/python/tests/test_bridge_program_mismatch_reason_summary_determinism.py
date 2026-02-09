from __future__ import annotations

from pathlib import Path

from formal.python.tools.bridge_program_mismatch_reason_summary import (
    build_bridge_program_mismatch_reason_summary,
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


def test_bridge_program_mismatch_reason_summary_is_deterministic() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    r1 = build_bridge_program_mismatch_reason_summary(repo_root=repo_root)
    r2 = build_bridge_program_mismatch_reason_summary(repo_root=repo_root)

    assert r1 == r2
    assert r1.get("schema_version") == 1
    assert r1.get("report_id") == "BRIDGE_PROGRAM_MISMATCH_REASON_SUMMARY"

    recommended = dict(r1.get("recommended_next_target", {}))
    assert recommended.get("reason_code") == "none"
    assert recommended.get("suggested_design_ticket") == "BRIDGE_TICKET_PROGRAM_COMPLETE"
