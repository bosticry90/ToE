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
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
SEAM_REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_class_b_inventory_surface_is_pinned() -> None:
    text = _read(INVENTORY_PATH)

    required = (
        "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0",
        "TOE_MASTER_ACTION_CLASS_B_INVENTORY_STATUS_v0: ACTIVE_AUDIT_v0_NONCLAIM",
        "TOE_CLASS_B_PROMOTION_PILOT_SEAM_v0: SEAM-EM-QFT",
        "TOE_CLASS_B_PROMOTION_PILOT_CLASS_v0: TOE_CK_CLASS_COMPATIBILITY_v0",
        "TOE_CLASS_B_PROMOTION_PILOT_TARGET_v0: DERIVATION_TARGET_EM_QFT_CLASS_B_SEAM_PROMOTION_CYCLE01_v0",
        "TOE_CLASS_B_PROMOTION_PILOT_WITNESS_PACKAGE_v0: formal/toe_formal/ToeFormal/Constraints/SeamWitnessPackages.lean",
        "formal/docs/paper/DERIVATION_TARGET_EM_QFT_CLASS_B_SEAM_PROMOTION_CYCLE01_v0.md",
        "formal/python/tests/test_toe_master_action_class_b_inventory_gate.py",
    )
    for token in required:
        assert token in text, f"Inventory missing token `{token}`."


def test_class_b_inventory_rows_cover_known_seams() -> None:
    text = _read(INVENTORY_PATH)
    for seam_id in (
        "SEAM-EM-QFT",
        "SEAM-GR-QM",
        "SEAM-QM-STAT",
        "SEAM-STAT-QM",
        "SEAM-COSMO-SR",
        "SEAM-SR-COSMO",
    ):
        assert seam_id in text, f"Missing class-B inventory row for `{seam_id}`."


def test_class_b_inventory_is_cross_surface_pinned() -> None:
    reg_text = _read(SEAM_REGISTRY_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)

    inventory_rel = "formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
    pilot_rel = "formal/docs/paper/DERIVATION_TARGET_EM_QFT_CLASS_B_SEAM_PROMOTION_CYCLE01_v0.md"
    witness_rel = "formal/toe_formal/ToeFormal/Constraints/SeamWitnessPackages.lean"

    assert inventory_rel in reg_text
    assert pilot_rel in reg_text
    assert witness_rel in reg_text

    for ref in (inventory_rel, pilot_rel, witness_rel):
        assert ref in roadmap_text
        assert ref in state_text
