from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
FULL_INDEX_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "redundancy_control_seam_family_index_full_20260409_v0.json"
)
ARCHIVED_PILOT_INDEX_PATH = (
    REPO_ROOT
    / "archive"
    / "output"
    / "reports"
    / "redundancy_control_seam_family_index_20260409_v0.json"
)
ACTIVE_PILOT_INDEX_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "redundancy_control_seam_family_index_20260409_v0.json"
)
DEDUP_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "REDUNDANCY_CONTROL_SEAM_DEDUP_WAVE2_DECLARATION_20260409_v0.md"
)
DEDUP_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "redundancy_control_seam_dedup_wave2_20260409_v0.json"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_redundancy_control_seam_family_index_wave2_shape() -> None:
    full_payload = _json(FULL_INDEX_PATH)
    archived_payload = _json(ARCHIVED_PILOT_INDEX_PATH)
    dedup_payload = _json(DEDUP_REPORT_PATH)

    assert not ACTIVE_PILOT_INDEX_PATH.exists(), (
        "Seam pilot singleton must be retired from active reports after Wave 2 de-dup."
    )

    assert full_payload.get("schema_id") == "REDUNDANCY_CONTROL_SEAM_FAMILY_INDEX_FULL_20260409_v0"
    assert archived_payload.get("schema_id") == "REDUNDANCY_CONTROL_SEAM_FAMILY_INDEX_20260409_v0"

    full_families = full_payload.get("families")
    assert isinstance(full_families, list)
    assert any(f.get("family_id") == "SEAM_QM_STAT_CLASS_B_PHYSICS_PILOT" for f in full_families)

    assert dedup_payload.get("schema_id") == "REDUNDANCY_CONTROL_SEAM_DEDUP_WAVE2_20260409_v0"
    assert dedup_payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
    assert dedup_payload.get("family_id") == "SEAM_QM_STAT_CLASS_B_PHYSICS_PILOT"
    assert dedup_payload.get("active_surface_removed") == (
        "formal/output/reports/redundancy_control_seam_family_index_20260409_v0.json"
    )
    assert dedup_payload.get("archived_surface_path") == (
        "archive/output/reports/redundancy_control_seam_family_index_20260409_v0.json"
    )
    assert dedup_payload.get("active_authority_surface") == (
        "formal/output/reports/redundancy_control_seam_family_index_full_20260409_v0.json"
    )

    declaration_pointer = dedup_payload.get("dedup_declaration_pointer")
    assert declaration_pointer == (
        "formal/docs/release/REDUNDANCY_CONTROL_SEAM_DEDUP_WAVE2_DECLARATION_20260409_v0.md"
    )
    assert DEDUP_DECLARATION_PATH.exists(), "Seam Wave 2 de-dup declaration must exist."


def test_redundancy_control_seam_family_index_state_tokens_present() -> None:
    state_text = _active_text(STATE_PATH)

    required = [
        "REDUNDANCY_CONTROL_SEAM_PILOT_STATUS_v0: SUPERSEDED_BY_FULL_INDEX_DEDUP_WAVE2",
        "REDUNDANCY_CONTROL_SEAM_PILOT_INDEX_ARCHIVED_v0: archive/output/reports/redundancy_control_seam_family_index_20260409_v0.json",
        "REDUNDANCY_CONTROL_SEAM_DEDUP_WAVE2_DECLARATION_v0: formal/docs/release/REDUNDANCY_CONTROL_SEAM_DEDUP_WAVE2_DECLARATION_20260409_v0.md",
        "REDUNDANCY_CONTROL_SEAM_DEDUP_WAVE2_REPORT_v0: formal/output/reports/redundancy_control_seam_dedup_wave2_20260409_v0.json",
        "REDUNDANCY_CONTROL_SEAM_DEDUP_WAVE2_RULE_v0: PILOT_SINGLETON_SURFACE_MUST_BE_ARCHIVED_AND_FAMILY_COVERED_BY_FULL_INDEX",
        "REDUNDANCY_CONTROL_SEAM_PILOT_GATE_v0: formal/python/tests/test_redundancy_control_seam_family_index_gate.py",
    ]
    for token in required:
        assert token in state_text, f"Missing state token: {token}"
