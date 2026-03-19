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
CYCLE02_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_DISCHARGE_CYCLE02_v0.md"
CYCLE03_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_CLASS_FLIP_CYCLE03_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
CENTRAL_INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
THEOREM_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Bridges" / "GR_QM_SeamPromotion.lean"

CYCLE03_TARGET_REL = "formal/docs/paper/DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_CLASS_FLIP_CYCLE03_v0.md"
CYCLE03_GATE_REL = "formal/python/tests/test_gr_qm_seam_promotion_cycle03_class_flip_gate.py"
THEOREM_REL = "formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean"
AUTH_SYMBOL = "gr_qm_seam_cycle03_class_flip_authorization"
AUTH_BRIDGE_SYMBOL = "gr_qm_cycle02_to_cycle03_authorization_bridge"
AUTH_RETENTION_SYMBOL = "gr_qm_cycle03_authorization_retains_transport"
COMPLETION_PARITY_SYMBOL = "gr_qm_cycle03_completion_parity_package"
REGIME_CLOSURE_SYMBOL = "gr_qm_cycle03_regime_closure_semantics_package"
SHARED_DYNAMICS_TRANSPORT_SYMBOL = "gr_qm_cycle03_shared_dynamics_transport_semantics_package"
BLOCKER_DISCHARGE_PACKAGE_SYMBOL = "gr_qm_cycle03_transport_and_regime_closure_blocker_discharge_package"
EXPLICIT_BLOCKER_DISCHARGE_SYMBOL = "gr_qm_cycle03_shared_dynamics_transport_and_regime_closure_not_discharged_blocker_discharged"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_gr_qm_cycle03_class_flip_surface_and_parity() -> None:
    cycle02_target_text = _read(CYCLE02_TARGET_PATH)
    cycle03_target_text = _read(CYCLE03_TARGET_PATH)
    inventory_text = _read(INVENTORY_PATH)
    registry_text = _read(REGISTRY_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    central_inventory_text = _read(CENTRAL_INVENTORY_PATH)
    theorem_text = _read(THEOREM_PATH)

    assert "GR_QM_CLASS_B_PROMOTION_CYCLE02_STATUS_v0: PROOF_DISCHARGED_CLASS_B_PENDING_CLASS_FLIP_v0" in cycle02_target_text

    assert "GR_QM_CLASS_B_PROMOTION_CYCLE03_STATUS_v0: CLASS_A_PROMOTED_v0_NONCLAIM" in cycle03_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE03_AUTHORIZATION_THEOREM_v0: "
        f"{THEOREM_REL}#{AUTH_SYMBOL}"
    ) in cycle03_target_text
    assert f"GR_QM_CLASS_B_PROMOTION_CYCLE03_GATE_v0: {CYCLE03_GATE_REL}" in cycle03_target_text
    assert "GR_QM_CLASS_B_PROMOTION_CYCLE03_AUTHORIZATION_BRIDGE_STATUS_v0: EXPLICIT_BOUNDED_v0_NONCLAIM" in cycle03_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE03_AUTHORIZATION_BRIDGE_THEOREM_v0: "
        f"{THEOREM_REL}#{AUTH_BRIDGE_SYMBOL}"
    ) in cycle03_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE03_AUTHORIZATION_BRIDGE_DEPENDS_ON_v0: "
        "gr_qm_cycle02_retention_transport_contract"
    ) in cycle03_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE03_AUTHORIZATION_BRIDGE_CONCLUSION_v0: "
        "CYCLE03_CLASS_FLIP_AUTHORIZATION_SURFACE_ESTABLISHED"
    ) in cycle03_target_text
    assert "GR_QM_CLASS_B_PROMOTION_CYCLE03_AUTHORIZATION_RETENTION_STATUS_v0: EXPLICIT_BOUNDED_v0_NONCLAIM" in cycle03_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE03_AUTHORIZATION_RETENTION_THEOREM_v0: "
        f"{THEOREM_REL}#{AUTH_RETENTION_SYMBOL}"
    ) in cycle03_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE03_AUTHORIZATION_RETENTION_DEPENDS_ON_v0: "
        f"{AUTH_BRIDGE_SYMBOL}"
    ) in cycle03_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE03_AUTHORIZATION_RETENTION_CONCLUSION_v0: "
        "CYCLE03_AUTHORIZATION_PLUS_NO_SHORTCUT_TRANSPORT_RETAINED"
    ) in cycle03_target_text
    assert "GR_QM_CLASS_B_PROMOTION_CYCLE03_COMPLETION_PARITY_STATUS_v0: EXPLICIT_WIDER_TRANCHE_v0_NONCLAIM" in cycle03_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE03_COMPLETION_PARITY_THEOREM_v0: "
        f"{THEOREM_REL}#{COMPLETION_PARITY_SYMBOL}"
    ) in cycle03_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE03_COMPLETION_PARITY_DEPENDS_ON_v0: "
        "gr_qm_cycle03_class_flip_normalized_package"
    ) in cycle03_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE03_COMPLETION_PARITY_CONCLUSION_v0: "
        "CYCLE03_NORMALIZED_PACKAGE_PLUS_TOE_CK_CLASS_THEOREM_LINKED_TOKEN_EXPLICIT"
    ) in cycle03_target_text
    assert "GR_QM_CLASS_B_PROMOTION_CYCLE03_REGIME_CLOSURE_STATUS_v0: EXPLICIT_WIDER_TRANCHE_v0_NONCLAIM" in cycle03_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE03_REGIME_CLOSURE_THEOREM_v0: "
        f"{THEOREM_REL}#{REGIME_CLOSURE_SYMBOL}"
    ) in cycle03_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE03_REGIME_CLOSURE_DEPENDS_ON_v0: "
        f"{COMPLETION_PARITY_SYMBOL}"
    ) in cycle03_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE03_REGIME_CLOSURE_CONCLUSION_v0: "
        "CYCLE03_COMPLETION_PARITY_PACKAGE_PLUS_SHARED_DYNAMICS_REGIME_IDS_EXPLICIT"
    ) in cycle03_target_text
    assert "GR_QM_CLASS_B_PROMOTION_CYCLE03_SHARED_DYNAMICS_TRANSPORT_STATUS_v0: EXPLICIT_WIDER_TRANCHE_v0_NONCLAIM" in cycle03_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE03_SHARED_DYNAMICS_TRANSPORT_THEOREM_v0: "
        f"{THEOREM_REL}#{SHARED_DYNAMICS_TRANSPORT_SYMBOL}"
    ) in cycle03_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE03_SHARED_DYNAMICS_TRANSPORT_DEPENDS_ON_v0: "
        f"{REGIME_CLOSURE_SYMBOL}"
    ) in cycle03_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE03_SHARED_DYNAMICS_TRANSPORT_CONCLUSION_v0: "
        "CYCLE03_REGIME_CLOSURE_PACKAGE_PLUS_NO_SHORTCUT_TRANSPORT_TAG_EXPLICIT"
    ) in cycle03_target_text
    assert "GR_QM_CLASS_B_PROMOTION_CYCLE03_BLOCKER_DISCHARGE_PACKAGE_STATUS_v0: EXPLICIT_WIDER_TRANCHE_v0_NONCLAIM" in cycle03_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE03_BLOCKER_DISCHARGE_TARGET_TOKEN_v0: "
        "SHARED_DYNAMICS_TRANSPORT_AND_REGIME_CLOSURE_NOT_DISCHARGED"
    ) in cycle03_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE03_BLOCKER_DISCHARGE_RESOLUTION_v0: "
        "DISCHARGED_BY_SINGLE_BLOCKER_PACKAGE_THEOREM"
    ) in cycle03_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE03_BLOCKER_DISCHARGE_PACKAGE_THEOREM_v0: "
        f"{THEOREM_REL}#{BLOCKER_DISCHARGE_PACKAGE_SYMBOL}"
    ) in cycle03_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE03_BLOCKER_DISCHARGE_EXPLICIT_THEOREM_v0: "
        f"{THEOREM_REL}#{EXPLICIT_BLOCKER_DISCHARGE_SYMBOL}"
    ) in cycle03_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE03_BLOCKER_DISCHARGE_PACKAGE_DEPENDS_ON_v0: "
        f"{SHARED_DYNAMICS_TRANSPORT_SYMBOL}"
    ) in cycle03_target_text
    assert (
        "GR_QM_CLASS_B_PROMOTION_CYCLE03_BLOCKER_DISCHARGE_PACKAGE_CONCLUSION_v0: "
        "CYCLE03_SHARED_DYNAMICS_TRANSPORT_AND_REGIME_CLOSURE_COMPONENTS_EXPLICIT_IN_ONE_PACKAGE"
    ) in cycle03_target_text

    assert CYCLE03_TARGET_REL in inventory_text
    assert CYCLE03_GATE_REL in inventory_text
    assert "TOE_CLASS_B_PROMOTION_NEXT_PILOT_CLASS_FLIP_STATUS_v0: CLASS_A_PROMOTION_EXECUTED_v0" in inventory_text
    assert "| `SEAM-GR-QM` | `A` | `TOE_CK_CLASS_THEOREM_LINKED_v0` | `CLASS_A_PROMOTED_CYCLE03_v0` |" in inventory_text

    assert CYCLE03_TARGET_REL in registry_text
    assert CYCLE03_GATE_REL in registry_text
    assert "GR_QM_CLASS_B_PROMOTION_CYCLE03_STATUS_v0: CLASS_A_PROMOTED_v0_NONCLAIM" in registry_text

    for text in (roadmap_text,):
        assert CYCLE03_TARGET_REL in text
        assert CYCLE03_GATE_REL in text

    assert CYCLE03_TARGET_REL in state_text or CYCLE03_TARGET_REL in central_inventory_text
    assert CYCLE03_GATE_REL in state_text or CYCLE03_GATE_REL in central_inventory_text

    assert AUTH_SYMBOL in theorem_text
    assert AUTH_BRIDGE_SYMBOL in theorem_text
    assert AUTH_RETENTION_SYMBOL in theorem_text
    assert COMPLETION_PARITY_SYMBOL in theorem_text
    assert REGIME_CLOSURE_SYMBOL in theorem_text
    assert SHARED_DYNAMICS_TRANSPORT_SYMBOL in theorem_text
    assert BLOCKER_DISCHARGE_PACKAGE_SYMBOL in theorem_text
    assert EXPLICIT_BLOCKER_DISCHARGE_SYMBOL in theorem_text