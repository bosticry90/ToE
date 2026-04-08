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
AUTHORITY_SURFACE_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_FORMAL_VERIFICATION_AUTHORITY_SURFACE_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_SEAM_WITNESS_BRIDGE_INVENTORY_v0.md"


LEAN_SURFACES = [
    "formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean",
    "formal/toe_formal/ToeFormal/Bridges/EM_QFT_SeamPromotion.lean",
    "formal/toe_formal/ToeFormal/Bridges/BR01_DispersionToMetric.lean",
]


PY_GATES = [
    "formal/python/tests/test_gr_qm_seam_promotion_cycle01_theorem_gate.py",
    "formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py",
    "formal/python/tests/test_gr_qm_seam_promotion_cycle03_class_flip_gate.py",
    "formal/python/tests/test_em_qft_seam_promotion_cycle01_theorem_gate.py",
    "formal/python/tests/test_em_qft_seam_promotion_cycle02_discharge_gate.py",
    "formal/python/tests/test_em_qft_seam_promotion_cycle03_class_flip_gate.py",
    "formal/python/tests/test_br01_front_door_enforced.py",
]


EXAMPLE_ARTIFACTS = [
    "formal/output/qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
    "formal/output/qft_m4_seam_closure_promotion_cycle01_v0.json",
    "formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact.json",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_authority_and_inventory_surfaces_exist() -> None:
    assert AUTHORITY_SURFACE_PATH.exists(), "Formal authority surface is missing"
    assert INVENTORY_PATH.exists(), "Seam witness bridge inventory is missing"


def test_lean_bridge_surfaces_are_present_and_pinned() -> None:
    authority_text = _read(AUTHORITY_SURFACE_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for rel in LEAN_SURFACES:
        assert (REPO_ROOT / rel).exists(), f"Missing Lean bridge surface: {rel}"
        assert rel in authority_text, f"Authority surface missing Lean pointer: {rel}"
        assert rel in inventory_text, f"Inventory surface missing Lean pointer: {rel}"


def test_python_gate_surfaces_are_present_and_pinned() -> None:
    authority_text = _read(AUTHORITY_SURFACE_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for rel in PY_GATES:
        assert (REPO_ROOT / rel).exists(), f"Missing Python bridge gate: {rel}"
        gate_name = Path(rel).name
        assert gate_name in authority_text, f"Authority surface missing gate pointer: {gate_name}"
        assert gate_name in inventory_text, f"Inventory surface missing gate pointer: {gate_name}"


def test_example_artifact_surfaces_are_resolvable_and_pinned() -> None:
    authority_text = _read(AUTHORITY_SURFACE_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for rel in EXAMPLE_ARTIFACTS:
        assert (REPO_ROOT / rel).exists(), f"Missing example artifact surface: {rel}"
        assert rel in authority_text, f"Authority surface missing artifact pointer: {rel}"
        assert rel in inventory_text, f"Inventory surface missing artifact pointer: {rel}"
