from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
CHECKLIST_PATH = REPO_ROOT / "Canonical Verification Checklist.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "REDUNDANCY_CONTROL_CHANGELOG_ARCHIVE_DEDUP_WAVE7_DECLARATION_20260409_v0.md"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "redundancy_control_changelog_archive_dedup_wave7_20260409_v0.json"
)

ACTIVE_SURFACE_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_CHANGELOG_ARCHIVE_v0.md"
ARCHIVED_SURFACE_PATH = REPO_ROOT / "archive" / "docs" / "release" / "TOE_CHANGELOG_ARCHIVE_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_changelog_archive_dedup_wave7_shape() -> None:
    payload = _json(REPORT_PATH)
    state_text = _active_text(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)

    assert payload.get("schema_id") == "REDUNDANCY_CONTROL_CHANGELOG_ARCHIVE_DEDUP_WAVE7_20260409_v0"
    assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
    assert payload.get("family_id") == "CHANGELOG_SUPPORT_SURFACES"

    assert not ACTIVE_SURFACE_PATH.exists(), "Legacy active changelog surface must be removed from release path."
    assert ARCHIVED_SURFACE_PATH.exists(), "Archived changelog surface must exist in archive path."

    assert payload.get("active_surface_removed") == "formal/docs/release/TOE_CHANGELOG_ARCHIVE_v0.md"
    assert payload.get("archived_surface_path") == "archive/docs/release/TOE_CHANGELOG_ARCHIVE_v0.md"
    assert payload.get("active_authority_surface") == "State_of_the_Theory.md"
    assert payload.get("dedup_declaration_pointer") == (
        "formal/docs/release/REDUNDANCY_CONTROL_CHANGELOG_ARCHIVE_DEDUP_WAVE7_DECLARATION_20260409_v0.md"
    )
    assert DECLARATION_PATH.exists()

    assert "archive/docs/release/TOE_CHANGELOG_ARCHIVE_v0.md" in state_text
    assert "archive/docs/release/TOE_CHANGELOG_ARCHIVE_v0.md" in inventory_text


def test_changelog_archive_dedup_wave7_tokens_present() -> None:
    state_text = _active_text(STATE_PATH)
    checklist_text = _read(CHECKLIST_PATH)

    state_required = [
        "REDUNDANCY_CONTROL_CHANGELOG_ARCHIVE_DEDUP_WAVE7_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM",
        "REDUNDANCY_CONTROL_CHANGELOG_ARCHIVE_DEDUP_WAVE7_DECLARATION_v0: formal/docs/release/REDUNDANCY_CONTROL_CHANGELOG_ARCHIVE_DEDUP_WAVE7_DECLARATION_20260409_v0.md",
        "REDUNDANCY_CONTROL_CHANGELOG_ARCHIVE_DEDUP_WAVE7_REPORT_v0: formal/output/reports/redundancy_control_changelog_archive_dedup_wave7_20260409_v0.json",
        "REDUNDANCY_CONTROL_CHANGELOG_ARCHIVE_DEDUP_WAVE7_GATE_v0: formal/python/tests/test_redundancy_control_changelog_archive_dedup_wave7_gate.py",
    ]
    for token in state_required:
        assert token in state_text, f"Missing state token: {token}"

    checklist_required = [
        "Changelog archive Wave-7 declaration present? YES / NO",
        "Changelog active release surface archived? YES / NO",
        "Change posture authority remains in compact state and inventory? YES / NO",
    ]
    for token in checklist_required:
        assert token in checklist_text, f"Missing checklist token: {token}"