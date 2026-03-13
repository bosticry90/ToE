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
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"

REQUIRED_REFS = (
    "formal/docs/paper/DERIVATION_TARGET_TOE_QFT_SCALAR_ROUTE_v0.md",
    "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_COMPLETION_CRITERIA_v0.md",
    "formal/docs/paper/toe_qft_scalar_field_derivation_report_v0.md",
    "formal/output/toe_qft_scalar_field_equations_v0.json",
    "formal/docs/paper/toe_qft_scalar_covariance_report_v0.md",
    "formal/output/toe_qft_scalar_stress_energy_artifact_v0.json",
    "formal/docs/paper/toe_qft_scalar_canonical_quantization_report_v0.md",
    "formal/output/toe_qft_scalar_canonical_quantization_artifact_v0.json",
    "formal/docs/paper/toe_qft_scalar_canonical_momentum_report_v0.md",
    "formal/output/toe_qft_scalar_hamiltonian_density_artifact_v0.json",
    "formal/docs/paper/toe_qft_scalar_operator_commutator_report_v0.md",
    "formal/output/toe_qft_scalar_operator_commutator_artifact_v0.json",
    "formal/docs/paper/toe_qft_scalar_mode_expansion_report_v0.md",
    "formal/output/toe_qft_scalar_creation_annihilation_artifact_v0.json",
    "formal/docs/paper/toe_qft_scalar_normalization_report_v0.md",
    "formal/output/toe_qft_scalar_one_particle_state_artifact_v0.json",
    "formal/docs/paper/toe_qft_scalar_nonrelativistic_limit_report_v0.md",
    "formal/output/toe_qft_scalar_schrodinger_limit_artifact_v0.json",
    "formal/docs/paper/toe_qft_scalar_propagator_report_v0.md",
    "formal/output/toe_qft_scalar_two_point_function_artifact_v0.json",
    "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_MILESTONE_SUMMARY_v0.md",
    "formal/output/toe_qft_scalar_route_milestone_checkpoint_v0.json",
    "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_REVIEW_READINESS_v0.md",
    "formal/output/toe_qft_scalar_route_review_readiness_checkpoint_v0.json",
    "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_MANUSCRIPT_SKELETON_v0.md",
    "formal/output/toe_qft_scalar_route_section_map_v0.json",
    "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_MANUSCRIPT_DRAFT_v0.md",
    "formal/output/toe_qft_scalar_route_manuscript_fill_map_v0.json",
    "formal/output/toe_qft_scalar_route_citation_binding_map_v0.json",
    "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_BIBLIOGRAPHY_ALIGNMENT_v0.md",
    "formal/output/toe_qft_scalar_route_reference_map_v0.json",
    "formal/python/tests/test_toe_qft_scalar_route_charter_gate.py",
    "formal/python/tests/test_toe_qft_scalar_field_equation_gate.py",
    "formal/python/tests/test_toe_qft_scalar_covariance_gate.py",
    "formal/python/tests/test_toe_qft_scalar_quantization_gate.py",
    "formal/python/tests/test_toe_qft_scalar_hamiltonian_gate.py",
    "formal/python/tests/test_toe_qft_scalar_operator_commutator_gate.py",
    "formal/python/tests/test_toe_qft_scalar_mode_expansion_gate.py",
    "formal/python/tests/test_toe_qft_scalar_normalization_gate.py",
    "formal/python/tests/test_toe_qft_scalar_nonrelativistic_limit_gate.py",
    "formal/python/tests/test_toe_qft_scalar_propagator_gate.py",
    "formal/python/tests/test_toe_qft_scalar_route_milestone_gate.py",
    "formal/python/tests/test_toe_qft_scalar_route_review_readiness_gate.py",
    "formal/python/tests/test_toe_qft_scalar_route_manuscript_skeleton_gate.py",
    "formal/python/tests/test_toe_qft_scalar_route_manuscript_draft_gate.py",
    "formal/python/tests/test_toe_qft_scalar_route_citation_binding_gate.py",
    "formal/python/tests/test_toe_qft_scalar_route_bibliography_alignment_gate.py",
    "formal/python/tests/test_toe_qft_scalar_route_parity_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_toe_qft_scalar_route_cross_surface_pointer_parity() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    for ref in REQUIRED_REFS:
        assert ref in state_text, f"Scalar-route pointer missing from State_of_the_Theory.md: {ref}"
        assert ref in roadmap_text, f"Scalar-route pointer missing from PHYSICS_ROADMAP_v0.md: {ref}"


def test_toe_qft_scalar_route_referenced_surfaces_exist() -> None:
    for ref in REQUIRED_REFS:
        path = REPO_ROOT / ref
        assert path.exists(), f"Scalar-route parity pointer target does not exist: {ref}"
