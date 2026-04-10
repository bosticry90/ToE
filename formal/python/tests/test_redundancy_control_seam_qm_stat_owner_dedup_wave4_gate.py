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
    / "REDUNDANCY_CONTROL_SEAM_QM_STAT_OWNER_DEDUP_WAVE4_DECLARATION_20260409_v0.md"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "redundancy_control_seam_qm_stat_owner_dedup_wave4_20260409_v0.json"
)

ACTIVE_OWNER_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_CLASS_B_SEAM_PILOT_STATUS.md"
ARCHIVED_OWNER_PATH = REPO_ROOT / "archive" / "docs" / "paper" / "TOE_CLASS_B_SEAM_PILOT_STATUS.md"
FULL_OWNER_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE11_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_seam_qm_stat_owner_dedup_wave4_shape() -> None:
    payload = _json(REPORT_PATH)
    full_index = _json(FULL_INDEX_PATH)

    assert payload.get("schema_id") == "REDUNDANCY_CONTROL_SEAM_QM_STAT_OWNER_DEDUP_WAVE4_20260409_v0"
    assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
    assert payload.get("family_id") == "SEAM_QM_STAT_CLASS_B_PHYSICS_PILOT"

    assert not ACTIVE_OWNER_PATH.exists(), "Legacy active owner surface must be removed from active paper path."
    assert ARCHIVED_OWNER_PATH.exists(), "Legacy owner surface must exist in archive path."
    assert FULL_OWNER_PATH.exists(), "Active full-index owner surface must exist."

    assert payload.get("active_owner_surface_removed") == "formal/docs/paper/TOE_CLASS_B_SEAM_PILOT_STATUS.md"
    assert payload.get("archived_owner_surface_path") == "archive/docs/paper/TOE_CLASS_B_SEAM_PILOT_STATUS.md"
    assert payload.get("active_full_index_owner_surface") == (
        "formal/docs/paper/DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE11_v0.md"
    )
    assert payload.get("declaration_pointer") == (
        "formal/docs/release/REDUNDANCY_CONTROL_SEAM_QM_STAT_OWNER_DEDUP_WAVE4_DECLARATION_20260409_v0.md"
    )
    assert DECLARATION_PATH.exists()

    families = full_index.get("families")
    assert isinstance(families, list)
    qm_stat = [f for f in families if f.get("family_id") == "SEAM_QM_STAT_CLASS_B_PHYSICS_PILOT"]
    assert len(qm_stat) == 1
    assert qm_stat[0].get("canonical_owner") == (
        "formal/docs/paper/DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE11_v0.md"
    )


def test_seam_qm_stat_owner_dedup_wave4_tokens_present() -> None:
    state_text = _active_text(STATE_PATH)
    checklist_text = _read(CHECKLIST_PATH)

    state_required = [
        "REDUNDANCY_CONTROL_SEAM_QM_STAT_OWNER_DEDUP_WAVE4_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM",
        "REDUNDANCY_CONTROL_SEAM_QM_STAT_OWNER_DEDUP_WAVE4_DECLARATION_v0: formal/docs/release/REDUNDANCY_CONTROL_SEAM_QM_STAT_OWNER_DEDUP_WAVE4_DECLARATION_20260409_v0.md",
        "REDUNDANCY_CONTROL_SEAM_QM_STAT_OWNER_DEDUP_WAVE4_REPORT_v0: formal/output/reports/redundancy_control_seam_qm_stat_owner_dedup_wave4_20260409_v0.json",
        "REDUNDANCY_CONTROL_SEAM_QM_STAT_OWNER_DEDUP_WAVE4_GATE_v0: formal/python/tests/test_redundancy_control_seam_qm_stat_owner_dedup_wave4_gate.py",
    ]
    for token in state_required:
        assert token in state_text, f"Missing state token: {token}"

    checklist_required = [
        "Seam QM-STAT owner Wave-4 declaration present? YES / NO",
        "Seam QM-STAT legacy owner surface archived? YES / NO",
        "Seam QM-STAT full-index owner unchanged? YES / NO",
    ]
    for token in checklist_required:
        assert token in checklist_text, f"Missing checklist token: {token}"
