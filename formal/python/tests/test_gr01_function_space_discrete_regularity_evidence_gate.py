from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
NOTE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_EVIDENCE_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "gr01_function_space_discrete_regularity_evidence_v0.json"
ANALYTIC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_ANALYTIC_DISCHARGE_v0.md"
WEAK_FIELD_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Variational" / "WeakFieldPoissonLimit.lean"
DISCRETE_FIELD_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Variational" / "DiscreteField.lean"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_gr01_function_space_row01_has_concrete_discrete_regularity_evidence() -> None:
    note_text = _read(NOTE_PATH)
    analytic_text = _read(ANALYTIC_PATH)
    weak_field_text = _read(WEAK_FIELD_PATH)
    discrete_field_text = _read(DISCRETE_FIELD_PATH)
    artifact = json.loads(_read(ARTIFACT_PATH))

    for token in (
        "GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_STATUS_v0: DISCHARGED_v0_CONCRETE_EVIDENCE_NONCLAIM",
        "GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_CLASS_v0: FINITE_DISCRETE_LATTICE_SCALAR_FIELD_CLASS",
        "GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_WITNESS_1D_v0: ScalarField1D",
        "GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_WITNESS_3D_v0: ScalarField3D",
        "GR01_FUNCTION_SPACE_DISCRETE_BOUNDARY_POSTURE_v0: EXPLICIT_PERIODIC_OR_DISCRETE_BOUNDARY_CONVENTIONS",
    ):
        assert token in note_text

    assert "regularity posture in v0 is discrete bounded-field regularity on finite-domain points" in analytic_text
    assert "abbrev ScalarField1D := Int → Real" in weak_field_text
    assert "abbrev ScalarField3D := LatticePoint3D → Real" in weak_field_text
    assert "abbrev FieldGrid (nx ny : Nat) : Type :=" in discrete_field_text

    assert artifact["artifact_id"] == "gr01_function_space_discrete_regularity_evidence_v0"
    assert artifact["status"] == "DISCHARGED_v0_CONCRETE_EVIDENCE_NONCLAIM"
    assert artifact["regularity_class"] == "FINITE_DISCRETE_LATTICE_SCALAR_FIELD_CLASS"
    assert set(artifact["witnesses"]) == {"ScalarField1D", "ScalarField3D", "FieldGrid"}

    for text in (_read(STATE_PATH), _read(ROADMAP_PATH)):
        assert "formal/docs/paper/TOE_GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_EVIDENCE_v0.md" in text
        assert "formal/output/gr01_function_space_discrete_regularity_evidence_v0.json" in text
        assert "formal/python/tests/test_gr01_function_space_discrete_regularity_evidence_gate.py" in text