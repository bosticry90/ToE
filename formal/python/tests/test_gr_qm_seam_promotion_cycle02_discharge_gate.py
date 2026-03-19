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
CYCLE01_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_CYCLE01_v0.md"
CYCLE02_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_DISCHARGE_CYCLE02_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
CENTRAL_INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
THEOREM_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Bridges" / "GR_QM_SeamPromotion.lean"

CYCLE02_TARGET_REL = "formal/docs/paper/DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_DISCHARGE_CYCLE02_v0.md"
DISCHARGE_GATE_REL = "formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py"
THEOREM_REL = "formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean"
DISCHARGE_THEOREM_SYMBOL = "gr_qm_seam_cycle02_discharge_proof"
BRIDGE_THEOREM_SYMBOL = "gr_qm_cycle02_class_b_retention_bridge"
PERSISTENCE_THEOREM_SYMBOL = "gr_qm_cycle02_compatibility_tag_persistence"
NO_SHORTCUT_TOKEN = "NO_SHORTCUT_PROMOTION_CHECKLIST_PINNED_v0"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_gr_qm_cycle02_discharge_surface_and_parity() -> None:
    cycle01_target_text = _read(CYCLE01_TARGET_PATH)
    cycle02_target_text = _read(CYCLE02_TARGET_PATH)
    inventory_text = _read(INVENTORY_PATH)
    registry_text = _read(REGISTRY_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    central_inventory_text = _read(CENTRAL_INVENTORY_PATH)
    theorem_text = _read(THEOREM_PATH)

    assert "GR_QM_CLASS_B_PROMOTION_CYCLE01_STATUS_v0: THEOREM_POINTER_PINNED_PENDING_PROOF_DISCHARGE" in cycle01_target_text

    assert "GR_QM_CLASS_B_PROMOTION_CYCLE02_STATUS_v0: PROOF_DISCHARGED_CLASS_B_PENDING_CLASS_FLIP_v0" in cycle02_target_text
    assert "GR_QM_CLASS_B_PROMOTION_CYCLE02_THEOREM_STATUS_v0: DISCHARGED_BOUNDED_v0_NONCLAIM" in cycle02_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE02_DISCHARGE_THEOREM_v0: "
        f"{THEOREM_REL}#{DISCHARGE_THEOREM_SYMBOL}"
    ) in cycle02_target_text
    assert f"GR_QM_CLASS_B_PROMOTION_CYCLE02_DISCHARGE_GATE_v0: {DISCHARGE_GATE_REL}" in cycle02_target_text
    assert "GR_QM_CLASS_B_PROMOTION_CYCLE02_BRIDGE_STATEMENT_STATUS_v0: EXPLICIT_BOUNDED_v0_NONCLAIM" in cycle02_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE02_BRIDGE_STATEMENT_THEOREM_v0: "
        f"{THEOREM_REL}#{BRIDGE_THEOREM_SYMBOL}"
    ) in cycle02_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE02_BRIDGE_STATEMENT_CONCLUSION_v0: "
        "CLASS_B_COMPATIBILITY_SURFACE_RETAINED"
    ) in cycle02_target_text
    assert "GR_QM_CLASS_B_PROMOTION_CYCLE02_COMPATIBILITY_PERSISTENCE_STATUS_v0: EXPLICIT_BOUNDED_v0_NONCLAIM" in cycle02_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE02_COMPATIBILITY_PERSISTENCE_THEOREM_v0: "
        f"{THEOREM_REL}#{PERSISTENCE_THEOREM_SYMBOL}"
    ) in cycle02_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE02_COMPATIBILITY_PERSISTENCE_DEPENDS_ON_v0: "
        f"{BRIDGE_THEOREM_SYMBOL}"
    ) in cycle02_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE02_COMPATIBILITY_PERSISTENCE_CONCLUSION_v0: "
        "TOE_CK_CLASS_COMPATIBILITY_v0_RETAINED"
    ) in cycle02_target_text
    assert "GR_QM_CLASS_B_PROMOTION_CLASS_v0: B_RETAINED_v0" in cycle02_target_text

    assert CYCLE02_TARGET_REL in inventory_text
    assert DISCHARGE_GATE_REL in inventory_text

    for text in (registry_text, roadmap_text):
        assert CYCLE02_TARGET_REL in text
        assert DISCHARGE_GATE_REL in text

    assert CYCLE02_TARGET_REL in state_text or CYCLE02_TARGET_REL in central_inventory_text
    assert DISCHARGE_GATE_REL in state_text or DISCHARGE_GATE_REL in central_inventory_text

    assert DISCHARGE_THEOREM_SYMBOL in theorem_text
    assert BRIDGE_THEOREM_SYMBOL in theorem_text
    assert PERSISTENCE_THEOREM_SYMBOL in theorem_text
    assert NO_SHORTCUT_TOKEN in theorem_text