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
CHECKLIST_PATH = REPO_ROOT / "Canonical Verification Checklist.md"
DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "REDUNDANCY_CONTROL_DEDUP_WAVE_PROGRESS_20260409_v0.md"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "redundancy_control_dedup_wave_progress_20260409_v0.json"
)

REGISTRY_ACTIVE_SINGLETON = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "redundancy_control_registry_family_index_20260409_v0.json"
)
REGISTRY_ARCHIVED_SINGLETON = (
    REPO_ROOT
    / "archive"
    / "output"
    / "reports"
    / "redundancy_control_registry_family_index_20260409_v0.json"
)
SEAM_ACTIVE_SINGLETON = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "redundancy_control_seam_family_index_20260409_v0.json"
)
SEAM_ARCHIVED_SINGLETON = (
    REPO_ROOT
    / "archive"
    / "output"
    / "reports"
    / "redundancy_control_seam_family_index_20260409_v0.json"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_redundancy_control_dedup_wave_progress_shape() -> None:
    payload = _json(REPORT_PATH)

    assert payload.get("schema_id") == "REDUNDANCY_CONTROL_DEDUP_WAVE_PROGRESS_20260409_v0"
    assert payload.get("status") == "ACTIVE_NONLIVE_NONCLAIM"
    assert payload.get("admission_scope_required") == "REGISTRY_FULL_PLUS_SEAM_FULL_FAMILY_INDEXES"

    waves = payload.get("completed_waves")
    assert isinstance(waves, list)
    assert len(waves) == 2

    assert not REGISTRY_ACTIVE_SINGLETON.exists()
    assert not SEAM_ACTIVE_SINGLETON.exists()
    assert REGISTRY_ARCHIVED_SINGLETON.exists()
    assert SEAM_ARCHIVED_SINGLETON.exists()

    for wave in waves:
        declaration = wave.get("declaration")
        report = wave.get("report")
        archived = wave.get("archived_path")

        assert isinstance(declaration, str) and declaration
        assert isinstance(report, str) and report
        assert isinstance(archived, str) and archived

        assert (REPO_ROOT / declaration).exists(), f"Missing wave declaration: {declaration}"
        assert (REPO_ROOT / report).exists(), f"Missing wave report: {report}"
        assert (REPO_ROOT / archived).exists(), f"Missing archived singleton: {archived}"


def test_redundancy_control_dedup_wave_progress_tokens_present() -> None:
    state_text = _active_text(STATE_PATH)
    checklist_text = _read(CHECKLIST_PATH)

    state_required = [
        "REDUNDANCY_CONTROL_DEDUP_WAVE_PROGRESS_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM",
        "REDUNDANCY_CONTROL_DEDUP_WAVE_PROGRESS_DECLARATION_v0: formal/docs/release/REDUNDANCY_CONTROL_DEDUP_WAVE_PROGRESS_20260409_v0.md",
        "REDUNDANCY_CONTROL_DEDUP_WAVE_PROGRESS_REPORT_v0: formal/output/reports/redundancy_control_dedup_wave_progress_20260409_v0.json",
        "REDUNDANCY_CONTROL_DEDUP_WAVE_PROGRESS_GATE_v0: formal/python/tests/test_redundancy_control_dedup_wave_progress_gate.py",
    ]
    for token in state_required:
        assert token in state_text, f"Missing state token: {token}"

    checklist_required = [
        "De-dup wave progress declaration present? YES / NO",
        "Completed wave singleton paths archived and absent from active reports? YES / NO",
        "Admission semantics remains full-index scoped? YES / NO",
    ]
    for token in checklist_required:
        assert token in checklist_text, f"Missing checklist token: {token}"
