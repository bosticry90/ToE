from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SURFACE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_FUNCTION_SPACE_REGULARITY_SURFACE_v0.md"
NOTE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_EVIDENCE_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "gr01_function_space_discrete_regularity_evidence_v0.json"
ANALYTIC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_ANALYTIC_DISCHARGE_v0.md"
WEAK_FIELD_NOTE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_WEAK_FIELD_EXPANSION_NOTE_v0.md"
WEAK_FIELD_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Variational" / "WeakFieldPoissonLimit.lean"
DISCRETE_FIELD_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Variational" / "DiscreteField.lean"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_gr01_function_space_row01_has_concrete_discrete_regularity_evidence() -> None:
    surface_text = _read(SURFACE_PATH)
    note_text = _read(NOTE_PATH)
    analytic_text = _read(ANALYTIC_PATH)
    weak_field_note_text = _read(WEAK_FIELD_NOTE_PATH)
    weak_field_text = _read(WEAK_FIELD_PATH)
    discrete_field_text = _read(DISCRETE_FIELD_PATH)
    artifact = json.loads(_read(ARTIFACT_PATH))

    for token in (
        "GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_STATUS_v0: DISCHARGED_v0_CONCRETE_EVIDENCE_NONCLAIM",
        "GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_CLASS_v0: FINITE_DISCRETE_LATTICE_SCALAR_FIELD_CLASS",
        "GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_WITNESS_1D_v0: ScalarField1D",
        "GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_WITNESS_3D_v0: ScalarField3D",
        "GR01_FUNCTION_SPACE_DISCRETE_BOUNDARY_POSTURE_v0: EXPLICIT_PERIODIC_OR_DISCRETE_BOUNDARY_CONVENTIONS",
        "GR01_BOUNDARY_TERM_LOCAL_LEMMA_STATUS_v0: EXPLICIT_v0_DISCRETE_SCOPE_NONCLAIM",
        "GR01_BOUNDARY_TERM_LOCAL_LEMMA_NAME_v0: PERIODIC_DISCRETE_SUMMATION_BY_PARTS_BOUNDARY_CANCELLATION",
        "GR01_BOUNDARY_TERM_LOCAL_LEMMA_HYPOTHESES_v0: FINITE_DISCRETE_LATTICE_PLUS_BOUNDED_NEAREST_NEIGHBOR_DIFFERENCES",
        "GR01_BOUNDARY_TERM_LOCAL_LEMMA_CONCLUSION_v0: BOUNDARY_PAIRING_CANCELED_INTERIOR_TERM_RETAINS_BOUNDED_REGULARITY",
    ):
        assert token in note_text

    for token in (
        "GR01_BOUNDARY_TERM_LOCAL_LEMMA_STATUS_v0: EXPLICIT_v0_DISCRETE_SCOPE_NONCLAIM",
        "GR01_BOUNDARY_TERM_LOCAL_LEMMA_NAME_v0: PERIODIC_DISCRETE_SUMMATION_BY_PARTS_BOUNDARY_CANCELLATION",
    ):
        assert token in surface_text

    assert "regularity posture in v0 is discrete bounded-field regularity on finite-domain points" in analytic_text
    assert "endpoint pairing cancels exactly under that contract" in analytic_text
    assert "explicit local boundary-term regularity lemma for the discrete summation-by-parts step" in weak_field_note_text
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