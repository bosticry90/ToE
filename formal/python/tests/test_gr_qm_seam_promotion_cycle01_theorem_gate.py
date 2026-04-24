from __future__ import annotations

from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_CYCLE01_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
CENTRAL_INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
THEOREM_POINTER_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Bridges" / "GR_QM_SeamPromotion.lean"

THEOREM_POINTER_REL = "formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean"
THEOREM_POINTER_SYMBOL = "gr_qm_seam_cycle01_theorem_pointer"
THEOREM_GATE_REL = "formal/python/tests/test_gr_qm_seam_promotion_cycle01_theorem_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_gr_qm_cycle01_theorem_pointer_is_cross_surface_pinned() -> None:
    target_text = _read(TARGET_PATH)
    inventory_text = _read(INVENTORY_PATH)
    registry_text = _read(REGISTRY_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    central_inventory_text = _read(CENTRAL_INVENTORY_PATH)
    theorem_text = _read(THEOREM_POINTER_PATH)

    assert "GR_QM_CLASS_B_PROMOTION_CYCLE01_STATUS_v0: THEOREM_POINTER_PINNED_PENDING_PROOF_DISCHARGE" in target_text
    assert "GR_QM_CLASS_B_PROMOTION_CYCLE01_THEOREM_STATUS_v0: THEOREM_POINTER_PINNED_v0_NONCLAIM" in target_text
    assert f"GR_QM_CLASS_B_PROMOTION_CYCLE01_THEOREM_POINTER_v0: {THEOREM_POINTER_REL}#{THEOREM_POINTER_SYMBOL}" in target_text
    assert f"GR_QM_CLASS_B_PROMOTION_CYCLE01_THEOREM_GATE_v0: {THEOREM_GATE_REL}" in target_text

    for text in (inventory_text, registry_text, roadmap_text):
        assert "formal/docs/paper/DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_CYCLE01_v0.md" in text
        assert THEOREM_POINTER_REL in text
        assert THEOREM_GATE_REL in text

    assert "formal/docs/paper/DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_CYCLE01_v0.md" in state_text or "formal/docs/paper/DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_CYCLE01_v0.md" in central_inventory_text
    assert THEOREM_POINTER_REL in state_text or THEOREM_POINTER_REL in central_inventory_text
    assert THEOREM_GATE_REL in state_text or THEOREM_GATE_REL in central_inventory_text

    assert THEOREM_POINTER_SYMBOL in theorem_text
