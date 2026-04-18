from __future__ import annotations

from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_EM_U1_MICRO_21_DISTRIBUTIONAL_LANE_AUTHORIZATION_SCAFFOLD_v0.md"
)
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_em_u1_micro21_gate_surfaces_exist() -> None:
    assert DOC_PATH.exists(), "Missing EM U1 micro21 derivation target surface"
    assert INVENTORY_PATH.exists(), "Missing inventory surface"
    assert STATE_PATH.exists(), "Missing compact state surface"


def test_em_u1_micro21_doc_contains_authorization_tokens() -> None:
    text = _read(DOC_PATH)
    required_tokens = [
        "DERIVATION_TARGET_EM_U1_MICRO_21_DISTRIBUTIONAL_LANE_AUTHORIZATION_SCAFFOLD_v0",
        "AUTHZ_LANE_ID: ASM-EM-U1-MATH-DISTRIB-01",
        "EM_U1_DISTRIBUTIONAL_LANE_AUTHORIZATION_ROUTE_v0: ASSUMPTION_ID_GATED_IMPORT_PERMISSION_PINNED",
        "EM_U1_DISTRIBUTIONAL_LANE_AUTHORIZATION_NO_PROMOTION_v0: AUTHORIZATION_ONLY_NO_DISCHARGE",
        "EM_U1_MICRO21_DISTRIBUTIONAL_AUTHORIZATION_ADJUDICATION: NOT_YET_DISCHARGED",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "Missing required EM U1 micro21 authorization token(s): " + ", ".join(missing)


def test_em_u1_micro21_inventory_gate_pointer_is_pinned() -> None:
    inventory = _read(INVENTORY_PATH)
    assert "INV-PHYS-EM-U1-MICRO21" in inventory
    assert "formal/python/tests/test_em_u1_micro21_distributional_lane_authorization_scaffold_gate.py" in inventory
    assert "OPEN_PROOF_DEBT" in inventory


def test_em_u1_micro21_state_surface_has_route_and_adjudication_tokens() -> None:
    state = _read(STATE_PATH)
    assert "DERIVATION_TARGET_EM_U1_MICRO_21_DISTRIBUTIONAL_LANE_AUTHORIZATION_SCAFFOLD_v0.md" in state
    assert "EM_U1_DISTRIBUTIONAL_LANE_AUTHORIZATION_ROUTE_v0: ASSUMPTION_ID_GATED_IMPORT_PERMISSION_PINNED" in state
    assert "EM_U1_MICRO21_DISTRIBUTIONAL_AUTHORIZATION_ADJUDICATION: NOT_YET_DISCHARGED" in state
