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


def test_bridge_program_frontier_targets_is_deterministic() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    r1 = build_bridge_program_frontier_targets(repo_root=repo_root)
    r2 = build_bridge_program_frontier_targets(repo_root=repo_root)

    assert r1 == r2
    assert r1.get("schema_version") == 1
    assert r1.get("report_id") == "BRIDGE_PROGRAM_FRONTIER_TARGETS"

    summary = dict(r1.get("summary", {}))
    assert list(summary.get("target_reason_codes", [])) == list(DEFAULT_TARGET_REASONS)

