from __future__ import annotations

from pathlib import Path

from formal.python.tools.bridge_program_orthogonality_mismatch_report_generate import (
    build_bridge_program_orthogonality_mismatch_report,
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


def test_bridge_program_orthogonality_mismatch_report_is_deterministic() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    r1 = build_bridge_program_orthogonality_mismatch_report(repo_root=repo_root)
    r2 = build_bridge_program_orthogonality_mismatch_report(repo_root=repo_root)

    assert r1 == r2
    assert r1.get("schema_version") == 1
    assert r1.get("report_id") == "BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT"
    assert isinstance(r1.get("artifact_sha256"), str) and len(r1["artifact_sha256"]) == 64
