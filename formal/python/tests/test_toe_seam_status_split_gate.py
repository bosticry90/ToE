from __future__ import annotations

from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
STANDARD_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_SEAM_STATUS_SEMANTICS_STANDARD_v0.md"
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
CENTRAL_INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_seam_status_standard_and_snapshot_are_cross_pinned() -> None:
    standard_text = _read(STANDARD_PATH)
    registry_text = _read(REGISTRY_PATH)
    inventory_text = _read(INVENTORY_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    central_inventory_text = _read(CENTRAL_INVENTORY_PATH)

    for token in (
        "TOE_SEAM_STATUS_SEMANTICS_STANDARD_v0",
        "TOE_SEAM_STATUS_SEMANTICS_STATUS_v0: CANONICAL_PINNED",
        "SEAM_STATUS_CLASS_A_NOT_PHYSICS_COMPLETE_v0: TRUE",
    ):
        assert token in standard_text

    for token in (
        "SEAM_EM_QFT_GOVERNANCE_COMPLETE_v0: YES",
        "SEAM_EM_QFT_PHYSICS_COMPLETE_v0: NO",
        "SEAM_GR_QM_GOVERNANCE_COMPLETE_v0: YES",
        "SEAM_GR_QM_PHYSICS_COMPLETE_v0: NO",
        "SEAM_QM_STAT_GOVERNANCE_COMPLETE_v0: NO",
        "SEAM_QM_STAT_PHYSICS_COMPLETE_v0: NO",
        "SEAM_STAT_QM_GOVERNANCE_COMPLETE_v0: NO",
        "SEAM_STAT_QM_PHYSICS_COMPLETE_v0: NO",
        "SEAM_COSMO_SR_GOVERNANCE_COMPLETE_v0: NO",
        "SEAM_COSMO_SR_PHYSICS_COMPLETE_v0: NO",
    ):
        assert token in registry_text
        assert token in inventory_text

    for token in (
        "SEAM_EM_QFT_GOVERNANCE_COMPLETE_v0: YES",
        "SEAM_EM_QFT_PHYSICS_COMPLETE_v0: NO",
        "SEAM_GR_QM_GOVERNANCE_COMPLETE_v0: YES",
        "SEAM_GR_QM_PHYSICS_COMPLETE_v0: NO",
        "SEAM_QM_STAT_GOVERNANCE_COMPLETE_v0: NO",
        "SEAM_QM_STAT_PHYSICS_COMPLETE_v0: NO",
        "SEAM_STAT_QM_GOVERNANCE_COMPLETE_v0: NO",
        "SEAM_STAT_QM_PHYSICS_COMPLETE_v0: NO",
        "SEAM_COSMO_SR_GOVERNANCE_COMPLETE_v0: NO",
        "SEAM_COSMO_SR_PHYSICS_COMPLETE_v0: NO",
        "SEAM_SR_COSMO_GOVERNANCE_COMPLETE_v0: NO",
        "SEAM_SR_COSMO_PHYSICS_COMPLETE_v0: NO",
    ):
        assert token in registry_text
        assert token in inventory_text

    for text in (roadmap_text,):
        assert "formal/docs/release/TOE_SEAM_STATUS_SEMANTICS_STANDARD_v0.md" in text
        assert "formal/python/tests/test_toe_seam_status_split_gate.py" in text

    assert (
        "formal/docs/release/TOE_SEAM_STATUS_SEMANTICS_STANDARD_v0.md" in state_text
        or "formal/docs/release/TOE_SEAM_STATUS_SEMANTICS_STANDARD_v0.md" in central_inventory_text
    )
    assert (
        "formal/python/tests/test_toe_seam_status_split_gate.py" in state_text
        or "formal/python/tests/test_toe_seam_status_split_gate.py" in central_inventory_text
    )