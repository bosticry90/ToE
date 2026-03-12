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
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_toe_master_action_seam_registry_surface_is_pinned() -> None:
    registry_text = _read(REGISTRY_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)

    for token in (
        "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0",
        "TOE_MASTER_ACTION_SEAM_REGISTRY_STATUS_v0: SCAFFOLD_PINNED_NONCLAIM",
        "TOE_CK_CLASS_COMPATIBILITY_v0",
        "TOE_CK_CLASS_THEOREM_LINKED_v0",
        "TOE_CK_CLASS_BRIDGE_ADMISSIBILITY_v0",
        "TOE_CK_CLASS_TRANSPORT_CONSISTENCY_v0",
        "TOE_CK_CLASS_REGIME_INTERFACE_BOUNDEDNESS_v0",
        "formal/python/tests/test_toe_master_action_seam_registry_gate.py",
        "formal/docs/paper/DERIVATION_TARGET_EM_QFT_CLASS_B_SEAM_PROMOTION_CLASS_FLIP_CYCLE03_v0.md",
        "formal/python/tests/test_em_qft_seam_promotion_cycle03_class_flip_gate.py",
        "EM_QFT_CLASS_B_PROMOTION_CYCLE03_STATUS_v0: CLASS_A_PROMOTED_v0_NONCLAIM",
    ):
        assert token in registry_text, f"Registry missing token `{token}`."

    reg_rel = "formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"
    assert reg_rel in roadmap_text, "Roadmap must pin seam registry doc."
    assert reg_rel in state_text, "State must pin seam registry doc."
