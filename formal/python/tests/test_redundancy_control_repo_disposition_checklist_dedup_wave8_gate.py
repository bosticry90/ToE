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
DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "REDUNDANCY_CONTROL_REPO_DISPOSITION_CHECKLIST_DEDUP_WAVE8_DECLARATION_20260409_v0.md"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "redundancy_control_repo_disposition_checklist_dedup_wave8_20260409_v0.json"
)
RETENTION_POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "REPOSITORY_RETENTION_POLICY_v0.md"

ACTIVE_SURFACE_PATH = REPO_ROOT / "formal" / "docs" / "release" / "REPO_PROMOTE_ARCHIVE_PRUNE_CHECKLIST_v0.md"
ARCHIVED_SURFACE_PATH = REPO_ROOT / "archive" / "docs" / "release" / "REPO_PROMOTE_ARCHIVE_PRUNE_CHECKLIST_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_repo_disposition_checklist_dedup_wave8_shape() -> None:
    payload = _json(REPORT_PATH)
    state_text = _active_text(STATE_PATH)

    assert payload.get("schema_id") == "REDUNDANCY_CONTROL_REPO_DISPOSITION_CHECKLIST_DEDUP_WAVE8_20260409_v0"
    assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
    assert payload.get("family_id") == "REPO_DISPOSITION_SUPPORT_SURFACES"

    assert not ACTIVE_SURFACE_PATH.exists(), "Legacy active repo disposition checklist must be removed from release path."
    assert ARCHIVED_SURFACE_PATH.exists(), "Archived repo disposition checklist must exist in archive path."
    assert RETENTION_POLICY_PATH.exists(), "Repository retention policy authority surface must remain active."

    assert payload.get("active_surface_removed") == "formal/docs/release/REPO_PROMOTE_ARCHIVE_PRUNE_CHECKLIST_v0.md"
    assert payload.get("archived_surface_path") == "archive/docs/release/REPO_PROMOTE_ARCHIVE_PRUNE_CHECKLIST_v0.md"
    assert payload.get("active_authority_surface") == "formal/docs/release/REPOSITORY_RETENTION_POLICY_v0.md"
    assert payload.get("dedup_declaration_pointer") == (
        "formal/docs/release/REDUNDANCY_CONTROL_REPO_DISPOSITION_CHECKLIST_DEDUP_WAVE8_DECLARATION_20260409_v0.md"
    )
    assert DECLARATION_PATH.exists()

    assert "archive/docs/release/REPO_PROMOTE_ARCHIVE_PRUNE_CHECKLIST_v0.md" in state_text


def test_repo_disposition_checklist_dedup_wave8_tokens_present() -> None:
    state_text = _active_text(STATE_PATH)
    checklist_text = _read(CHECKLIST_PATH)

    state_required = [
        "REDUNDANCY_CONTROL_REPO_DISPOSITION_CHECKLIST_DEDUP_WAVE8_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM",
        "REDUNDANCY_CONTROL_REPO_DISPOSITION_CHECKLIST_DEDUP_WAVE8_DECLARATION_v0: formal/docs/release/REDUNDANCY_CONTROL_REPO_DISPOSITION_CHECKLIST_DEDUP_WAVE8_DECLARATION_20260409_v0.md",
        "REDUNDANCY_CONTROL_REPO_DISPOSITION_CHECKLIST_DEDUP_WAVE8_REPORT_v0: formal/output/reports/redundancy_control_repo_disposition_checklist_dedup_wave8_20260409_v0.json",
        "REDUNDANCY_CONTROL_REPO_DISPOSITION_CHECKLIST_DEDUP_WAVE8_GATE_v0: formal/python/tests/test_redundancy_control_repo_disposition_checklist_dedup_wave8_gate.py",
    ]
    for token in state_required:
        assert token in state_text, f"Missing state token: {token}"

    checklist_required = [
        "Repo disposition checklist Wave-8 declaration present? YES / NO",
        "Repo disposition active release surface archived? YES / NO",
        "Repository retention policy remains active authority? YES / NO",
    ]
    for token in checklist_required:
        assert token in checklist_text, f"Missing checklist token: {token}"