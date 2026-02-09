from __future__ import annotations

from pathlib import Path

from formal.python.tools.bridge_program_tolerance_tightening_delta_manifest_generate import (
    build_bridge_program_tolerance_tightening_delta_manifest,
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


def test_bridge_program_tolerance_tightening_delta_manifest_is_deterministic() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    r1 = build_bridge_program_tolerance_tightening_delta_manifest(repo_root=repo_root)
    r2 = build_bridge_program_tolerance_tightening_delta_manifest(repo_root=repo_root)

    assert r1 == r2
    assert r1.get("schema_version") == 1
    assert r1.get("report_id") == "BRIDGE_PROGRAM_TOLERANCE_TIGHTENING_DELTA_MANIFEST"
    assert isinstance(r1.get("artifact_sha256"), str) and len(r1["artifact_sha256"]) == 64
