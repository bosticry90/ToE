from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
GATE_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_COMPLETENESS_GATE_v0.md"
ROADMAP_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
CHECKLIST_DOC = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR01_DERIVATION_GRADE_CHECKLIST_v0.md"
)
THEORY_SPEC_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "THEORY_SPEC_v1.md"
TAXONOMY_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "CLAIM_TAXONOMY_v0.md"
OUTLINE_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_PAPER_OUTLINE_v0.md"
ANALYTIC_DISCHARGE_DOC = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_ANALYTIC_DISCHARGE_v0.md"
)
CANONICAL_EQUIV_DOC = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_CANONICAL_EQUIVALENCE_THEOREM_v0.md"
)
WEAKFIELD_LEAN = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Variational" / "WeakFieldPoissonLimit.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required artifact: {path.as_posix()}"
    return path.read_text(encoding="utf-8")


def test_derivation_completeness_gate_doc_is_present_and_tokenized() -> None:
    gate = _read(GATE_DOC)
    for token in [
        "DERIVATION_COMPLETENESS_GATE_v0",
        "TARGET-GR01-DERIV-COMPLETENESS-GATE-PLAN",
        "Gate Layers (All Required)",
        "Analytic discharge completeness",
        "Mainstream equivalence proof",
        "TOE_GR01_CANONICAL_EQUIVALENCE_THEOREM_v0.md",
        "TOE-GR01-EQUIV-01",
        "Assumption minimization audit",
        "Literature alignment mapping",
        "Mandatory Failure Triggers",
        "missing integration-by-parts step",
        "missing boundary-term handling",
        "missing function-space/regularity class",
        "missing constants normalization/units mapping",
        "missing canonical equivalence theorem",
        "nabla^2 Phi = kappa * rho",
        "Current gate posture for GR01: `CLOSED` (v0 discrete-only).",
    ]:
        assert token in gate, f"Derivation completeness gate doc missing token: {token}"


def test_derivation_completeness_gate_is_pinned_in_roadmap_and_checklist() -> None:
    roadmap = _read(ROADMAP_DOC)
    checklist = _read(CHECKLIST_DOC)
    for token in [
        "TARGET-GR01-DERIV-COMPLETENESS-GATE-PLAN",
        "DERIVATION_COMPLETENESS_GATE_v0.md",
        "Derivation completeness gate semantics (publication-grade tier):",
        "DERIVATION_COMPLETENESS_GATE",
    ]:
        assert token in roadmap, f"Roadmap missing derivation completeness gate token: {token}"

    for token in [
        "Derivation completeness gate (publication-grade tier; required before publishable promotion):",
        "TARGET-GR01-DERIV-COMPLETENESS-GATE-PLAN",
        "DERIVATION_COMPLETENESS_GATE_v0.md",
        "mainstream equivalence proof to canonical weak-field form `nabla^2 Phi = kappa * rho`",
        "assumption minimization audit",
        "literature alignment mapping",
    ]:
        assert token in checklist, f"GR01 derivation checklist missing gate token: {token}"


def test_publication_grade_boundary_is_bound_to_gate_policy_surfaces() -> None:
    theory_spec = _read(THEORY_SPEC_DOC)
    taxonomy = _read(TAXONOMY_DOC)
    outline = _read(OUTLINE_DOC)

    for token in [
        "publication-grade derivation gate (v0 policy):",
        "`T-PROVED` theorem shape is not sufficient by itself for publication-grade derivation claims.",
        "TARGET-GR01-DERIV-COMPLETENESS-GATE-PLAN",
        "analytic discharge completeness",
        "mainstream equivalence proof",
        "assumption minimization audit",
        "literature alignment mapping",
    ]:
        assert token in theory_spec, f"Theory spec missing publication-grade gate token: {token}"

    for token in [
        "Publication-grade derivation gate rule (all pillars, v0 policy)",
        "`T-PROVED` is necessary but not sufficient for publication-grade derivation claims.",
        "TARGET-GR01-DERIV-COMPLETENESS-GATE-PLAN",
        "DERIVATION_COMPLETENESS_GATE_v0.md",
    ]:
        assert token in taxonomy, f"Claim taxonomy missing publication-grade gate token: {token}"

    assert "## 7. Equivalence And Literature Mapping" in outline, (
        "Physics paper outline must preserve explicit equivalence/literature-mapping section."
    )


def test_derivation_completeness_discharge_package_anchors_are_present_in_gr01_analytic_note() -> None:
    analytic = _read(ANALYTIC_DISCHARGE_DOC)
    for token in [
        "## Function-Space / Regularity / Boundary Posture (v0)",
        "## Integration-By-Parts And Boundary-Term Handling (explicit v0 narrative)",
        "## Constants Normalization And Canonical Form Mapping (scoped)",
        "## Assumption Minimization Audit (v0 snapshot)",
        "## Assumption Minimization Delta (v0 closure step)",
        "assumption-minimization status: `DISCHARGED` (v0 discrete-only).",
        "## Literature Alignment Mapping (v0 discrete-only CLOSED)",
        "literature-alignment status: `DISCHARGED` (v0 discrete-only).",
        "ASM-GR01-BND-01",
        "ASM-GR01-NRM-01",
        "ASM-GR01-CAL-01",
        "kappa",
        "4πG",
        "canonical-equivalence theorem status: `DISCHARGED`",
        "publication-grade derivation completeness gate status is `CLOSED` (v0 discrete-only)",
        "TOE-GR01-EQUIV-01",
        "TOE_GR01_CANONICAL_EQUIVALENCE_THEOREM_v0.md",
    ]:
        assert token in analytic, (
            "GR01 analytic discharge note must include derivation-completeness discharge-package "
            f"anchor token: {token}"
        )
    assert "canonical-equivalence theorem remains an explicit open discharge item" not in analytic, (
        "GR01 analytic discharge note must not retain stale open-status canonical-equivalence wording "
        "after DISCHARGED state is pinned."
    )


def test_canonical_equivalence_theorem_artifact_and_lean_token_are_present() -> None:
    equiv = _read(CANONICAL_EQUIV_DOC)
    weakfield_lean = _read(WEAKFIELD_LEAN)

    for token in [
        "TOE_GR01_CANONICAL_EQUIVALENCE_THEOREM_v0",
        "TOE-GR01-EQUIV-01",
        "DiscreteLaplacian1D Φ i = κ * ρ i",
        "poissonEquation1D_iff_discreteLaplacian1D_eq_kappa_rho",
        "poissonEquation3D_iff_discreteLaplacian3D_eq_kappa_rho",
        "gr01_end_to_end_poisson_equation_under_promoted_assumptions",
        "canonical-equivalence theorem status: `DISCHARGED`",
    ]:
        assert token in equiv, (
            f"Canonical-equivalence theorem artifact missing required token: {token}"
        )

    assert "theorem poissonEquation1D_iff_discreteLaplacian1D_eq_kappa_rho" in weakfield_lean, (
        "WeakFieldPoissonLimit.lean must include the canonical-equivalence theorem token "
        "poissonEquation1D_iff_discreteLaplacian1D_eq_kappa_rho."
    )
    assert "theorem poissonEquation3D_iff_discreteLaplacian3D_eq_kappa_rho" in weakfield_lean, (
        "WeakFieldPoissonLimit.lean must include the 3D canonical-equivalence theorem token "
        "poissonEquation3D_iff_discreteLaplacian3D_eq_kappa_rho."
    )
