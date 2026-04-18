from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
CHECKLIST_PATH = REPO_ROOT / "Canonical Verification Checklist.md"
FULL_INDEX_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "redundancy_control_seam_family_index_full_20260409_v0.json"
)
DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "REDUNDANCY_CONTROL_SEAM_HISTORY_ARCHIVE_DEDUP_WAVE5_DECLARATION_20260409_v0.md"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "redundancy_control_seam_history_archive_dedup_wave5_20260409_v0.json"
)

ACTIVE_SURFACE_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_SEAM_HISTORY_ARCHIVE_v0.md"
ARCHIVED_SURFACE_PATH = REPO_ROOT / "archive" / "docs" / "release" / "TOE_SEAM_HISTORY_ARCHIVE_v0.md"
ACTIVE_OWNER_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_SEAM_STATUS_SEMANTICS_STANDARD_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_seam_history_archive_dedup_wave5_shape() -> None:
    payload = _json(REPORT_PATH)
    full_index = _json(FULL_INDEX_PATH)

    assert payload.get("schema_id") == "REDUNDANCY_CONTROL_SEAM_HISTORY_ARCHIVE_DEDUP_WAVE5_20260409_v0"
    assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
    assert payload.get("family_id") == "SEAM_STATUS_SUPPORT_SURFACES"

    assert not ACTIVE_SURFACE_PATH.exists(), "Legacy active seam history surface must be removed from release path."
    assert ARCHIVED_SURFACE_PATH.exists(), "Archived seam history surface must exist in archive path."
    assert ACTIVE_OWNER_PATH.exists(), "Canonical seam status owner surface must remain active."

    assert payload.get("active_surface_removed") == "formal/docs/release/TOE_SEAM_HISTORY_ARCHIVE_v0.md"
    assert payload.get("archived_surface_path") == "archive/docs/release/TOE_SEAM_HISTORY_ARCHIVE_v0.md"
    assert payload.get("active_authority_surface") == "formal/docs/release/TOE_SEAM_STATUS_SEMANTICS_STANDARD_v0.md"
    assert payload.get("dedup_declaration_pointer") == (
        "formal/docs/release/REDUNDANCY_CONTROL_SEAM_HISTORY_ARCHIVE_DEDUP_WAVE5_DECLARATION_20260409_v0.md"
    )
    assert DECLARATION_PATH.exists()

    families = full_index.get("families")
    assert isinstance(families, list)
    assert len(families) >= 2


def test_seam_history_archive_dedup_wave5_tokens_present() -> None:
    state_text = _active_text(STATE_PATH)
    checklist_text = _read(CHECKLIST_PATH)

    state_required = [
        "REDUNDANCY_CONTROL_SEAM_HISTORY_ARCHIVE_DEDUP_WAVE5_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM",
        "REDUNDANCY_CONTROL_SEAM_HISTORY_ARCHIVE_DEDUP_WAVE5_DECLARATION_v0: formal/docs/release/REDUNDANCY_CONTROL_SEAM_HISTORY_ARCHIVE_DEDUP_WAVE5_DECLARATION_20260409_v0.md",
        "REDUNDANCY_CONTROL_SEAM_HISTORY_ARCHIVE_DEDUP_WAVE5_REPORT_v0: formal/output/reports/redundancy_control_seam_history_archive_dedup_wave5_20260409_v0.json",
        "REDUNDANCY_CONTROL_SEAM_HISTORY_ARCHIVE_DEDUP_WAVE5_GATE_v0: formal/python/tests/test_redundancy_control_seam_history_archive_dedup_wave5_gate.py",
    ]
    for token in state_required:
        assert token in state_text, f"Missing state token: {token}"

    checklist_required = [
        "Seam history archive Wave-5 declaration present? YES / NO",
        "Seam history active release surface archived? YES / NO",
        "Seam status semantics owner remains active? YES / NO",
    ]
    for token in checklist_required:
        assert token in checklist_text, f"Missing checklist token: {token}"