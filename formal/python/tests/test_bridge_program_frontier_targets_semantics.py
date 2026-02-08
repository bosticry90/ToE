from __future__ import annotations

from pathlib import Path

from formal.python.tools.bridge_program_frontier_targets import (
    DEFAULT_TARGET_REASONS,
    build_bridge_program_frontier_targets,
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


def test_bridge_program_frontier_targets_track_historical_frontier_reasons() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    payload = build_bridge_program_frontier_targets(repo_root=repo_root)

    summary = dict(payload.get("summary", {}))
    targets = [dict(t) for t in payload.get("targets", [])]
    by_reason = {str(t.get("reason_code")): t for t in targets}

    for reason in DEFAULT_TARGET_REASONS:
        assert reason in by_reason, f"Missing frontier target reason: {reason}"

    n_mismatch_total = int(summary.get("n_mismatch_total", 0))
    frontier_complete = bool(summary.get("frontier_complete"))
    recommended = str(payload.get("recommended_next_ticket", ""))

    if n_mismatch_total == 0:
        assert frontier_complete is True
        assert recommended == "BRIDGE_TICKET_PROGRAM_COMPLETE"
        for reason in DEFAULT_TARGET_REASONS:
            t = by_reason[reason]
            assert str(t.get("status")) == "resolved"
            assert list(t.get("selected_probe_ids", [])) == []
    else:
        open_targets = [t for t in targets if str(t.get("status")) == "open"]
        assert open_targets, "Expected at least one open frontier target when mismatches are present"
        for t in open_targets:
            assert int(t.get("count", 0)) > 0
            assert list(t.get("selected_probe_ids", [])), "Open frontier target must select at least one probe"
        assert recommended != "BRIDGE_TICKET_PROGRAM_COMPLETE"

