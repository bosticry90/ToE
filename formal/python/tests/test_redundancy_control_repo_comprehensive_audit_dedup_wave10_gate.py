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
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
CHECKLIST_PATH = REPO_ROOT / "Canonical Verification Checklist.md"
DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "REDUNDANCY_CONTROL_REPO_COMPREHENSIVE_AUDIT_DEDUP_WAVE10_DECLARATION_20260409_v0.md"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "redundancy_control_repo_comprehensive_audit_dedup_wave10_20260409_v0.json"
)

ACTIVE_SURFACE_PATH = REPO_ROOT / "formal" / "docs" / "release" / "REPO_COMPREHENSIVE_AUDIT_20260317_v0.md"
ARCHIVED_SURFACE_PATH = REPO_ROOT / "archive" / "docs" / "release" / "REPO_COMPREHENSIVE_AUDIT_20260317_v0.md"
AUTHORITY_OWNER_PATH = REPO_ROOT / "formal" / "docs" / "release" / "REPO_STATUS_AUDIT_20260315_v0.md"

ARCHIVED_POINTER = "archive/docs/release/REPO_COMPREHENSIVE_AUDIT_20260317_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_repo_comprehensive_audit_dedup_wave10_shape() -> None:
    payload = _json(REPORT_PATH)
    state_text = _active_text(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    assert payload.get("schema_id") == "REDUNDANCY_CONTROL_REPO_COMPREHENSIVE_AUDIT_DEDUP_WAVE10_20260409_v0"
    assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
    assert payload.get("family_id") == "REPO_AUDIT_SUPPORT_SURFACES"

    assert not ACTIVE_SURFACE_PATH.exists(), "Legacy active repo comprehensive audit surface must be removed."
    assert ARCHIVED_SURFACE_PATH.exists(), "Archived repo comprehensive audit surface must exist."
    assert AUTHORITY_OWNER_PATH.exists(), "Active repo status audit owner surface must remain active."

    assert payload.get("active_surface_removed") == "formal/docs/release/REPO_COMPREHENSIVE_AUDIT_20260317_v0.md"
    assert payload.get("archived_surface_path") == "archive/docs/release/REPO_COMPREHENSIVE_AUDIT_20260317_v0.md"
    assert payload.get("active_authority_surface") == "formal/docs/release/REPO_STATUS_AUDIT_20260315_v0.md"
    assert payload.get("dedup_declaration_pointer") == (
        "formal/docs/release/REDUNDANCY_CONTROL_REPO_COMPREHENSIVE_AUDIT_DEDUP_WAVE10_DECLARATION_20260409_v0.md"
    )
    assert DECLARATION_PATH.exists()

    assert ARCHIVED_POINTER in state_text
    assert ARCHIVED_POINTER in roadmap_text


def test_repo_comprehensive_audit_dedup_wave10_tokens_present() -> None:
    state_text = _active_text(STATE_PATH)
    checklist_text = _read(CHECKLIST_PATH)

    state_required = [
        "REDUNDANCY_CONTROL_REPO_COMPREHENSIVE_AUDIT_DEDUP_WAVE10_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM",
        "REDUNDANCY_CONTROL_REPO_COMPREHENSIVE_AUDIT_DEDUP_WAVE10_DECLARATION_v0: formal/docs/release/REDUNDANCY_CONTROL_REPO_COMPREHENSIVE_AUDIT_DEDUP_WAVE10_DECLARATION_20260409_v0.md",
        "REDUNDANCY_CONTROL_REPO_COMPREHENSIVE_AUDIT_DEDUP_WAVE10_REPORT_v0: formal/output/reports/redundancy_control_repo_comprehensive_audit_dedup_wave10_20260409_v0.json",
        "REDUNDANCY_CONTROL_REPO_COMPREHENSIVE_AUDIT_DEDUP_WAVE10_GATE_v0: formal/python/tests/test_redundancy_control_repo_comprehensive_audit_dedup_wave10_gate.py",
    ]
    for token in state_required:
        assert token in state_text, f"Missing state token: {token}"

    checklist_required = [
        "Repo comprehensive audit Wave-10 declaration present? YES / NO",
        "Repo comprehensive audit active release surface archived? YES / NO",
        "Audit parity pointers preserved across state and roadmap? YES / NO",
    ]
    for token in checklist_required:
        assert token in checklist_text, f"Missing checklist token: {token}"