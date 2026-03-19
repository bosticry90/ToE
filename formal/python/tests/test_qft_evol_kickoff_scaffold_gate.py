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
QFT_EVOL_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
QFT_EVOL_KICKOFF_GATE_PATH = "formal/python/tests/test_qft_evol_kickoff_scaffold_gate.py"
QFT_EVOL_BUILD_GATE_PATH = "formal/python/tests/test_lean_build_gate_qft_evol_object_scaffold.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_evol_authority_surfaces_exist() -> None:
    assert INVENTORY_PATH.exists(), "Missing TOE_MATH_PHYSICS_INVENTORY authority surface."


def test_qft_evol_target_contains_required_kickoff_tokens() -> None:
    text = _read(QFT_EVOL_TARGET_PATH)
    required_tokens = [
        "DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0",
        "TARGET-QFT-EVOL-PLAN",
        "QFT_EVOL_ADJUDICATION: NOT_YET_DISCHARGED",
        "QFT_EVOL_SCOPE_BOUNDARY_v0: CONTRACT_OBJECT_SCAFFOLD_ONLY_NONCLAIM",
        "QFT_EVOL_PREREQS_v0: TARGET-QFT-GAUGE-PLAN;TARGET-SR-COV-PLAN;TARGET-EM-U1-PLAN",
        "QFT_EVOL_DELIVERABLE_FIELD_OBJECT_v0: FIELD_CARRIER_TYPED_SCAFFOLD_ONLY",
        "QFT_EVOL_DELIVERABLE_LAGRANGIAN_PLACEHOLDER_v0: ACTION_DENSITY_PLACEHOLDER_NONCLAIM",
        "QFT_EVOL_DELIVERABLE_EOM_PLACEHOLDER_v0: EULER_LAGRANGE_STATEMENT_ONLY",
        "QFT_EVOL_DELIVERABLE_CANONICAL_MOMENTUM_PLACEHOLDER_v0: STATEMENT_ONLY",
        "QFT_EVOL_DELIVERABLE_UNITARITY_PLACEHOLDER_v0: STATEMENT_ONLY_NONPROOF",
        "formal/toe_formal/ToeFormal/QFT/Evolution/ObjectScaffold.lean",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution kickoff target is missing required token(s): " + ", ".join(missing)


def test_qft_roadmap_row_is_closed_and_contains_evol_surface_pointer() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    rows = [line.strip() for line in roadmap_text.splitlines() if line.strip().startswith("| `PILLAR-QFT` |")]
    assert len(rows) == 1, f"Expected exactly one PILLAR-QFT roadmap row, found {len(rows)}."
    row = rows[0]
    required_row_tokens = [
        "| `CLOSED` |",
        "TARGET-QFT-GAUGE-PLAN;TARGET-QFT-EVOL-PLAN",
        "formal/docs/paper/DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md",
    ]
    missing = [token for token in required_row_tokens if token not in row]
    assert not missing, "PILLAR-QFT roadmap row is missing required evolution token(s): " + ", ".join(missing)


def test_qft_evol_nonclaim_boundary_is_explicit() -> None:
    text = _read(QFT_EVOL_TARGET_PATH)
    required_nonclaim_phrases = [
        "This artifact is planning-only.",
        "This artifact does not claim quantization closure.",
        "This artifact does not claim dynamics derivation closure.",
        "This artifact does not claim Standard Model recovery.",
        "This artifact does not claim external truth.",
        "CONTRACT_OBJECT_SCAFFOLD_ONLY_NONCLAIM",
    ]
    missing = [phrase for phrase in required_nonclaim_phrases if phrase not in text]
    assert not missing, "QFT evolution kickoff non-claim boundary phrase(s) missing: " + ", ".join(missing)


def test_qft_evol_kickoff_and_build_gates_are_pinned_in_authority_surfaces() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for required_path in [QFT_EVOL_KICKOFF_GATE_PATH, QFT_EVOL_BUILD_GATE_PATH]:
        assert required_path in roadmap_text, (
            f"Roadmap authority surface must pin `{required_path}`."
        )
        assert required_path in state_text or required_path in inventory_text, (
            f"State or inventory authority surface must pin `{required_path}`."
        )
