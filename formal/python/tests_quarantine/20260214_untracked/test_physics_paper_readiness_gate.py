from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
STATE_DOC = REPO_ROOT / "State_of_the_Theory.md"
THEORY_SPEC_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "THEORY_SPEC_v1.md"
THEOREM_SURFACE_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_THEOREM_SURFACE_v0.md"
ANALYTIC_DISCHARGE_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_ANALYTIC_DISCHARGE_v0.md"
LAPLACIAN_NOTE_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_LAPLACIAN_EXTRACTION_v0.md"
ACTION_RAC_STANCE_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_ACTION_RAC_STANCE_v0.md"
CONSERVATION_COMPAT_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_CONSERVATION_COMPATIBILITY_v0.md"
OUTLINE_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_PAPER_OUTLINE_v0.md"
RESULTS_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"
POINT_SOURCE_TARGET_DOC = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_GR01_3D_POINT_SOURCE_CLASS_v0.md"
)
THEOREM_LEAN = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Variational" / "WeakFieldPoissonLimit.lean"
)
TRACKA_MAINSTREAM3D_LEAN = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "GR01Mainstream3DSpherical.lean"
)
TRACKB_MAINSTREAM3D_LEAN = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "GR01Mainstream3DPointSource.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required artifact: {path.as_posix()}"
    return path.read_text(encoding="utf-8")


def _lean_decl_body(text: str, decl_kind: str, decl_name: str) -> str:
    start_match = re.search(
        rf"(?m)^{decl_kind}\s+{re.escape(decl_name)}\b",
        text,
    )
    assert start_match is not None, f"Missing Lean declaration: {decl_kind} {decl_name}"
    tail = text[start_match.end() :]
    boundary = re.search(
        r"(?m)^(theorem\s+|def\s+|structure\s+|class\s+|abbrev\s+|instance\s+|axiom\s+|end\b)",
        tail,
    )
    return tail if boundary is None else tail[: boundary.start()]


def _lean_decl_signature(text: str, decl_kind: str, decl_name: str) -> str:
    start_match = re.search(
        rf"(?m)^{decl_kind}\s+{re.escape(decl_name)}\b",
        text,
    )
    assert start_match is not None, f"Missing Lean declaration: {decl_kind} {decl_name}"
    tail = text[start_match.start() :]
    end_match = re.search(r":=", tail)
    assert end_match is not None, f"Lean declaration must include ':=' body: {decl_kind} {decl_name}"
    return tail[: end_match.start()]


def test_gr01_3d_posture_units_and_falsifiability_tokens_are_present() -> None:
    state = _read(STATE_DOC)
    theory_spec = _read(THEORY_SPEC_DOC)
    theorem_surface = _read(THEOREM_SURFACE_DOC)
    analytic_discharge = _read(ANALYTIC_DISCHARGE_DOC)
    laplacian_note = _read(LAPLACIAN_NOTE_DOC)
    conservation_compat = _read(CONSERVATION_COMPAT_DOC)
    point_source_target = _read(POINT_SOURCE_TARGET_DOC)
    theorem_lean = _read(THEOREM_LEAN)
    tracka_mainstream3d_lean = _read(TRACKA_MAINSTREAM3D_LEAN)
    trackb_mainstream3d_lean = _read(TRACKB_MAINSTREAM3D_LEAN)

    for token in [
        "nabla_3D^2 Phi = kappa * rho",
        "DiscreteLaplacian3D",
        "PoissonEquation3D",
        "TOE-GR-3D-02",
        "TOE-GR-3D-03",
        "TARGET-GR01-3D-03-PLAN",
        "TOE-GR-CONS-01",
        "TOE_GR01_ACTION_RAC_STANCE_v0.md",
    ]:
        assert token in state, f"State doc missing GR01 physics-posture token: {token}"

    for token in [
        "## 9. 3D Posture And Falsifiability (GR01 Weak-Field)",
        "nabla_3D^2 Phi = kappa * rho",
        "DiscreteLaplacian3D",
        "DiscretePoissonResidual3D",
        "PoissonEquation3D",
        "Separable3DMappingAssumptions",
        "poissonEquation3D_of_componentwise_poissonEquation1D_under_separable",
        "Lift1DTo3DMappingAssumptions",
        "poissonEquation3D_of_poissonEquation1D_under_lift_x_only",
        "Falsifiability hooks:",
    ]:
        assert token in theory_spec, f"Theory spec missing 3D/falsifiability token: {token}"

    for token in [
        "PoissonEquation3D",
        "nabla_3D^2 Phi = kappa * rho",
        "Separable3DMappingAssumptions",
        "poissonEquation3D_of_componentwise_poissonEquation1D_under_separable",
        "Lift1DTo3DMappingAssumptions",
        "poissonEquation3D_of_poissonEquation1D_under_lift_x_only",
        "TOE-GR-3D-03",
        "mainstream-class 3D closure gate milestone",
        "gr01_mainstream3d_discrete_laplacian_reduces_to_radial_under_spherical_symmetry",
        "gr01_mainstream3d_discrete_residual_reduces_to_radial_under_spherical_symmetry",
        "gr01_mainstream3d_radial_poisson_away_from_source_from_operator_equation_under_spherical_symmetry",
        "gr01_mainstream3d_point_source_model_discrete_delta_or_shell",
        "gr01_mainstream3d_green_class_partial_surface_token",
        "SphericalOperatorEquationAwayFromSourceAssumptions",
        "operator_equation_3d_away_from_source",
        "radiusBound",
        "radial_index_realized_within_bound",
        "gr01_mainstream3d_point_source_partial_surface_token",
        "gr01_mainstream3d_point_source_bounded_potential_behavior_posture",
        "gr01_mainstream3d_point_source_residual_discharge_under_dirichlet_boundary",
        "gr01_mainstream3d_point_source_center_residual_defect_is_explicit_under_dirichlet_boundary",
        "gr01_mainstream3d_point_source_domain_residual_characterization_under_dirichlet_boundary",
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_under_dirichlet_boundary",
        "IsInteriorPoint",
        "SatisfiesDirichletLinearSystemOnDomain",
        "SatisfiesDirichletPoissonSystemOnDomain",
        "DirichletLinearOperator3D",
        "DirichletRHS3D",
        "OperatorEncodesDiscreteLaplacianOnInterior",
        "SatisfiesFiniteLinearOperatorEquationOnDomain",
        "OperatorHasDirichletRightInverseOnDomain",
        "PointSourceDirichletCandidateSolution",
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_derived_from_dirichlet_system",
        "gr01_mainstream3d_point_source_linear_system_satisfaction_from_operator_equation",
        "gr01_mainstream3d_point_source_system_satisfaction_from_linear_system",
        "gr01_mainstream3d_point_source_candidate_exists_from_linear_system",
        "gr01_mainstream3d_point_source_candidate_exists_from_operator_equation",
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_from_operator_equation",
        "gr01_mainstream3d_point_source_solution_exists_for_operator_equation_under_invertibility",
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_exists_from_operator_equation_under_invertibility",
        "This posture does not claim 3D derivation discharge is complete in v0.",
    ]:
        assert token in theorem_surface, f"Theorem surface missing 3D posture token: {token}"

    for token in [
        "## Units Dictionary (Scoped)",
        "## Falsifiability Hooks",
        "TOE_GR01_ACTION_RAC_STANCE_v0.md",
        "TOE-GR-3D-03",
        "TARGET-GR01-3D-03-PLAN",
        "gr01_mainstream3d_point_source_bounded_potential_behavior_posture",
        "Non-claim boundary:",
    ]:
        assert token in analytic_discharge, f"Analytic discharge note missing required token: {token}"

    for token in [
        "DiscreteLaplacian3D",
        "DiscretePoissonResidual3D",
        "PoissonEquation3D",
        "nabla_3D^2 Phi = kappa * rho",
        "Separable3DMappingAssumptions",
        "poissonEquation3D_of_componentwise_poissonEquation1D_under_separable",
        "Lift1DTo3DMappingAssumptions",
        "poissonEquation3D_of_poissonEquation1D_under_lift_x_only",
    ]:
        assert token in laplacian_note, f"Laplacian extraction note missing 3D posture token: {token}"

    for token in [
        "TOE_GR01_CONSERVATION_COMPATIBILITY_v0",
        "Minimal Compatibility Statement",
        "nabla · g = -kappa * rho",
        "B-BLOCKED",
    ]:
        assert token in conservation_compat, (
            f"GR01 conservation compatibility doc missing token: {token}"
        )

    for token in [
        "DERIVATION_TARGET_GR01_3D_POINT_SOURCE_CLASS_v0",
        "TARGET-GR01-3D-POINT-SOURCE-PLAN",
        "## Track B Residual Discharge Target (future upgrade; not yet satisfied)",
        "PointSourceDirichletBoundaryAssumptions",
        "gr01_mainstream3d_point_source_residual_discharge_under_dirichlet_boundary",
        "gr01_mainstream3d_point_source_center_residual_defect_is_explicit_under_dirichlet_boundary",
        "gr01_mainstream3d_point_source_domain_residual_characterization_under_dirichlet_boundary",
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_under_dirichlet_boundary",
        "FiniteDirichletDomain3D",
        "IsInteriorPoint",
        "SatisfiesDirichletLinearSystemOnDomain",
        "SatisfiesDirichletPoissonSystemOnDomain",
        "DirichletLinearOperator3D",
        "DirichletRHS3D",
        "OperatorEncodesDiscreteLaplacianOnInterior",
        "SatisfiesFiniteLinearOperatorEquationOnDomain",
        "OperatorHasDirichletRightInverseOnDomain",
        "PointSourceDirichletCandidateSolution",
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_derived_from_dirichlet_system",
        "gr01_mainstream3d_point_source_linear_system_satisfaction_from_operator_equation",
        "gr01_mainstream3d_point_source_system_satisfaction_from_linear_system",
        "gr01_mainstream3d_point_source_candidate_exists_from_linear_system",
        "gr01_mainstream3d_point_source_candidate_exists_from_operator_equation",
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_from_operator_equation",
        "gr01_mainstream3d_point_source_solution_exists_for_operator_equation_under_invertibility",
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_exists_from_operator_equation_under_invertibility",
        "candidate potential class:",
        "boundary condition class:",
        "stencil residual endpoint lemma:",
    ]:
        assert token in point_source_target, (
            f"Track B target doc missing residual-discharge anchor token: {token}"
        )

    for token in [
        "def DiscreteLaplacian3D",
        "def DiscretePoissonResidual3D",
        "def PoissonEquation3D",
        "def WeakFieldPoissonLimitStatement3D",
        "structure Lift1DTo3DMappingAssumptions",
        "structure Separable3DMappingAssumptions",
        "theorem discreteLaplacian3D_of_lift_x_only",
        "theorem discretePoissonResidual3D_of_lift_x_only",
        "theorem poissonEquation3D_of_poissonEquation1D_under_lift_x_only",
        "theorem discreteLaplacian3D_of_separable",
        "theorem discretePoissonResidual3D_of_separable",
        "theorem poissonEquation3D_of_componentwise_poissonEquation1D_under_separable",
    ]:
        assert token in theorem_lean, f"WeakFieldPoissonLimit.lean missing 3D token: {token}"

    for token in [
        "structure SphericalSymmetryMappingAssumptions",
        "structure SphericalOperatorEquationAwayFromSourceAssumptions",
        "laplacian_reduces_to_radial",
        "operator_equation_3d_away_from_source",
        "radiusBound",
        "radial_index_realized_within_bound",
        "RadialPoissonEquationAwayFromSourceWithinBound",
        "gr01_mainstream3d_discrete_laplacian_reduces_to_radial_under_spherical_symmetry",
        "gr01_mainstream3d_discrete_residual_reduces_to_radial_under_spherical_symmetry",
        "gr01_mainstream3d_radial_poisson_away_from_source_from_operator_equation_under_spherical_symmetry",
        "gr01_mainstream3d_point_source_model_discrete_delta_or_shell",
        "gr01_mainstream3d_green_class_partial_surface_token",
        "gr01_mainstream3d_poissonEquation3D_of_radial_poisson_under_spherical_symmetry",
        "gr01_mainstream3d_spherical_partial_surface_token",
    ]:
        assert token in tracka_mainstream3d_lean, (
            f"GR01Mainstream3DSpherical.lean missing Track A token: {token}"
        )

    for token in [
        "structure PointSourceMappingAssumptions",
        "structure PointSourceDirichletBoundaryAssumptions",
        "structure FiniteDirichletDomain3D",
        "def IsInteriorPoint",
        "def SatisfiesDirichletLinearSystemOnDomain",
        "def SatisfiesDirichletPoissonSystemOnDomain",
        "structure DirichletLinearOperator3D",
        "def DirichletRHS3D",
        "def OperatorEncodesDiscreteLaplacianOnInterior",
        "def SatisfiesFiniteLinearOperatorEquationOnDomain",
        "def OperatorHasDirichletRightInverseOnDomain",
        "structure PointSourceDirichletCandidateSolution",
        "structure PointSourceResidualDischargeUnderDirichlet",
        "delta_posture",
        "bounded_domain",
        "bounded_potential_behavior",
        "theorem gr01_mainstream3d_point_source_delta_posture_is_explicit",
        "theorem gr01_mainstream3d_point_source_bounded_domain_posture",
        "theorem gr01_mainstream3d_point_source_bounded_potential_behavior_posture",
        "theorem gr01_mainstream3d_point_source_poissonEquation3D_under_bounded_delta_posture",
        "theorem gr01_mainstream3d_point_source_partial_surface_token",
        "theorem gr01_mainstream3d_point_source_dirichlet_boundary_posture_is_explicit",
        "theorem gr01_mainstream3d_point_source_residual_zero_away_from_source_under_dirichlet_boundary",
        "theorem gr01_mainstream3d_point_source_center_residual_defect_is_explicit_under_dirichlet_boundary",
        "theorem gr01_mainstream3d_point_source_residual_discharge_under_dirichlet_boundary",
        "theorem gr01_mainstream3d_point_source_domain_residual_characterization_under_dirichlet_boundary",
        "theorem gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_under_dirichlet_boundary",
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_derived_from_dirichlet_system",
        "theorem gr01_mainstream3d_point_source_linear_system_satisfaction_from_operator_equation",
        "theorem gr01_mainstream3d_point_source_system_satisfaction_from_linear_system",
        "theorem gr01_mainstream3d_point_source_candidate_exists_from_linear_system",
        "theorem gr01_mainstream3d_point_source_candidate_exists_from_operator_equation",
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_from_operator_equation",
        "gr01_mainstream3d_point_source_solution_exists_for_operator_equation_under_invertibility",
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_exists_from_operator_equation_under_invertibility",
    ]:
        assert token in trackb_mainstream3d_lean, (
            f"GR01Mainstream3DPointSource.lean missing Track B token: {token}"
        )


def test_trackb_linear_system_and_poisson_system_definitions_are_semantically_separated() -> None:
    trackb_mainstream3d_lean = _read(TRACKB_MAINSTREAM3D_LEAN)
    results = _read(RESULTS_DOC)
    linear_body = _lean_decl_body(
        trackb_mainstream3d_lean,
        "def",
        "SatisfiesDirichletLinearSystemOnDomain",
    )
    assert "DiscreteLaplacian3D" in linear_body, (
        "SatisfiesDirichletLinearSystemOnDomain must stay equation-form and reference DiscreteLaplacian3D."
    )
    assert "DiscretePoissonResidual3D" not in linear_body, (
        "SatisfiesDirichletLinearSystemOnDomain must not directly reference DiscretePoissonResidual3D."
    )

    away_body = _lean_decl_body(
        trackb_mainstream3d_lean,
        "def",
        "PoissonEquation3DAwayFromSourceOnDomain",
    )
    assert "DiscretePoissonResidual3D" in away_body, (
        "PoissonEquation3DAwayFromSourceOnDomain must retain the residual predicate surface."
    )

    system_body = _lean_decl_body(
        trackb_mainstream3d_lean,
        "def",
        "SatisfiesDirichletPoissonSystemOnDomain",
    )
    assert (
        "PoissonEquation3DAwayFromSourceOnDomain" in system_body
        or "DiscretePoissonResidual3D" in system_body
    ), (
        "SatisfiesDirichletPoissonSystemOnDomain must remain tied to Poisson residual posture."
    )

    operator_equation_body = _lean_decl_body(
        trackb_mainstream3d_lean,
        "def",
        "SatisfiesFiniteLinearOperatorEquationOnDomain",
    )
    assert "A.apply" in operator_equation_body, (
        "SatisfiesFiniteLinearOperatorEquationOnDomain must remain operator-form and reference A.apply."
    )
    assert "DiscreteLaplacian3D" not in operator_equation_body, (
        "SatisfiesFiniteLinearOperatorEquationOnDomain must not directly reference DiscreteLaplacian3D."
    )

    bridge_body = _lean_decl_body(
        trackb_mainstream3d_lean,
        "theorem",
        "gr01_mainstream3d_point_source_linear_system_satisfaction_from_operator_equation",
    )
    assert "A.apply" in bridge_body, (
        "Operator-equation bridge theorem must reference A.apply to keep operator-layer semantics explicit."
    )
    assert "DiscreteLaplacian3D" in bridge_body, (
        "Operator-equation bridge theorem must connect to DiscreteLaplacian3D."
    )

    candidate_from_operator_body = _lean_decl_body(
        trackb_mainstream3d_lean,
        "theorem",
        "gr01_mainstream3d_point_source_candidate_exists_from_operator_equation",
    )
    assert "A.apply" in candidate_from_operator_body, (
        "Operator-to-candidate theorem must reference A.apply to preserve operator-layer semantics."
    )
    assert "PointSourceDirichletCandidateSolution" in candidate_from_operator_body, (
        "Operator-to-candidate theorem must retain candidate packaging semantics."
    )
    assert "DiscretePoissonResidual3D" not in candidate_from_operator_body, (
        "Operator-to-candidate theorem must not collapse directly to residual-form language."
    )

    away_from_operator_body = _lean_decl_body(
        trackb_mainstream3d_lean,
        "theorem",
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_from_operator_equation",
    )
    assert "A.apply" in away_from_operator_body, (
        "Operator-to-away-from-source theorem must reference A.apply to preserve operator-layer semantics."
    )
    assert "PoissonEquation3DAwayFromSourceOnDomain" in away_from_operator_body, (
        "Operator-to-away-from-source theorem must retain away-from-source closure semantics."
    )
    assert "DiscretePoissonResidual3D" not in away_from_operator_body, (
        "Operator-to-away-from-source theorem must not collapse directly to residual-form language."
    )

    invertibility_body = _lean_decl_body(
        trackb_mainstream3d_lean,
        "def",
        "OperatorHasDirichletRightInverseOnDomain",
    )
    assert "A.apply" in invertibility_body, (
        "OperatorHasDirichletRightInverseOnDomain must remain operator-form and reference A.apply."
    )
    assert "DiscretePoissonResidual3D" not in invertibility_body, (
        "OperatorHasDirichletRightInverseOnDomain must not collapse to residual-form language."
    )

    solver_signature = _lean_decl_signature(
        trackb_mainstream3d_lean,
        "theorem",
        "gr01_mainstream3d_point_source_solution_exists_for_operator_equation_under_invertibility",
    )
    assert "(Φ" not in solver_signature, (
        "Solver existence theorem must eliminate explicit Φ theorem inputs."
    )
    assert "∃ Φ" in solver_signature, (
        "Solver existence theorem must expose existential candidate output."
    )

    solver_body = _lean_decl_body(
        trackb_mainstream3d_lean,
        "theorem",
        "gr01_mainstream3d_point_source_solution_exists_for_operator_equation_under_invertibility",
    )
    assert ("A.apply" in solver_body) or ("hInterior" in solver_body), (
        "Solver existence theorem body must preserve operator-layer semantics."
    )
    assert "DirichletRHS3D" in solver_body, (
        "Solver existence theorem body must anchor RHS construction semantics."
    )
    assert "DiscretePoissonResidual3D" not in solver_body, (
        "Solver existence theorem must not collapse directly to residual-form language."
    )

    existential_closure_signature = _lean_decl_signature(
        trackb_mainstream3d_lean,
        "theorem",
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_exists_from_operator_equation_under_invertibility",
    )
    assert "(Φ" not in existential_closure_signature, (
        "Existential away-from-source theorem must eliminate explicit Φ theorem inputs."
    )
    assert "∃ Φ" in existential_closure_signature, (
        "Existential away-from-source theorem must expose existential closure output."
    )

    existential_closure_body = _lean_decl_body(
        trackb_mainstream3d_lean,
        "theorem",
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_exists_from_operator_equation_under_invertibility",
    )
    assert (
        "gr01_mainstream3d_point_source_solution_exists_for_operator_equation_under_invertibility"
        in existential_closure_body
    ), (
        "Existential away-from-source theorem must compose solver existence theorem."
    )
    assert (
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_from_operator_equation"
        in existential_closure_body
    ), (
        "Existential away-from-source theorem must compose operator-to-away-from-source theorem."
    )
    assert "DiscretePoissonResidual3D" not in existential_closure_body, (
        "Existential away-from-source theorem must not collapse directly to residual-form language."
    )

    assert re.search(
        r"^\|\s*TOE-GR-3D-PS-10\s*\|\s*`T-CONDITIONAL`\s*\|",
        results,
        flags=re.MULTILINE,
    ), "Readiness gate requires PS-10 to remain T-CONDITIONAL."
    assert re.search(
        r"^\|\s*TOE-GR-3D-PS-11\s*\|\s*`T-PROVED`\s*\|",
        results,
        flags=re.MULTILINE,
    ), "Readiness gate requires PS-11 to be promoted to T-PROVED."
    assert re.search(
        r"^\|\s*TOE-GR-3D-PS-12\s*\|\s*`T-PROVED`\s*\|",
        results,
        flags=re.MULTILINE,
    ), "Readiness gate requires PS-12 to be promoted to T-PROVED."


def test_tracka_green_class_bridge_is_derived_from_operator_equation_not_repackaged() -> None:
    tracka_mainstream3d_lean = _read(TRACKA_MAINSTREAM3D_LEAN)
    for banned in [
        "radial_index_surjective",
        "hOp.radial_index_surjective",
        "hGreen.bounded_domain",
    ]:
        assert banned not in tracka_mainstream3d_lean, (
            "Track A scaffold must not retain stale global-surjectivity or duplicated "
            f"green bounded-domain branch text: {banned}"
        )

    op_bridge_structure_body = _lean_decl_body(
        tracka_mainstream3d_lean,
        "structure",
        "SphericalOperatorEquationAwayFromSourceAssumptions",
    )
    assert "operator_equation_3d_away_from_source" in op_bridge_structure_body, (
        "Track A operator-bridge structure must expose operator-equation assumptions."
    )
    assert "radiusBound" in op_bridge_structure_body, (
        "Track A operator-bridge structure must expose an explicit bounded-shell radius."
    )
    assert "radial_index_realized_within_bound" in op_bridge_structure_body, (
        "Track A operator-bridge structure must use bounded radial-index coverage assumptions."
    )
    assert "radial_index_surjective" not in op_bridge_structure_body, (
        "Track A operator-bridge structure must not require global radial-index surjectivity."
    )
    assert "DiscretePoissonResidualRadial" not in op_bridge_structure_body, (
        "Track A operator-bridge structure must not encode radial residual closure directly."
    )

    green_structure_body = _lean_decl_body(
        tracka_mainstream3d_lean,
        "structure",
        "SphericalGreenClassPartialAssumptions",
    )
    assert "radial_operator_equation_away_from_source" not in green_structure_body, (
        "Track A green-class structure must not carry direct radial residual closure as a field."
    )
    assert "bounded_domain" not in green_structure_body, (
        "Track A green-class structure must not duplicate bounded-domain fields "
        "already carried by operator-bridge assumptions."
    )
    assert "operatorBridge" in green_structure_body, (
        "Track A green-class structure must depend on operator-bridge assumptions."
    )

    radial_bridge_body = _lean_decl_body(
        tracka_mainstream3d_lean,
        "theorem",
        "gr01_mainstream3d_radial_poisson_away_from_source_from_operator_equation_under_spherical_symmetry",
    )
    assert "operator_equation_3d_away_from_source" in radial_bridge_body, (
        "Track A radial away-from-source theorem must derive from 3D operator-equation assumptions."
    )
    assert "RadialPoissonEquationAwayFromSourceWithinBound" in radial_bridge_body, (
        "Track A radial away-from-source theorem must preserve bounded-domain closure semantics."
    )

    green_token_body = _lean_decl_body(
        tracka_mainstream3d_lean,
        "theorem",
        "gr01_mainstream3d_green_class_partial_surface_token",
    )
    assert (
        "gr01_mainstream3d_radial_poisson_away_from_source_from_operator_equation_under_spherical_symmetry"
        in green_token_body
    ), (
        "Track A green-class partial token must be composed from the derived radial bridge theorem."
    )


def test_action_rac_stance_and_physics_outline_are_present() -> None:
    action_rac = _read(ACTION_RAC_STANCE_DOC)
    outline = _read(OUTLINE_DOC)

    for token in [
        "TOE_GR01_ACTION_RAC_STANCE_v0",
        "Conservative conditional-derivation stance is selected.",
        "conditional-publish endpoint",
        "hAction",
        "hRAC",
        "Retirement Alignment Criteria",
        "Non-claim Boundary",
    ]:
        assert token in action_rac, f"Action/RAC stance doc missing token: {token}"

    for token in [
        "PHYSICS_PAPER_OUTLINE_v0",
        "Non-claim boundary:",
        "## 1. Model And Assumptions",
        "## 2. Derivation Chain (Primary Result)",
        "## 4. Limit Recoveries",
        "## 5. Falsifiability And Failure Modes",
    ]:
        assert token in outline, f"Physics paper outline missing token: {token}"
