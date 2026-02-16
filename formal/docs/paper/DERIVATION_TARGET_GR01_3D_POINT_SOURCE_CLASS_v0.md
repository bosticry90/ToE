# Derivation Target: GR01 3D Point-Source-Class Closure v0

Spec ID:
- `DERIVATION_TARGET_GR01_3D_POINT_SOURCE_CLASS_v0`

Target ID:
- `TARGET-GR01-3D-POINT-SOURCE-PLAN`

Classification:
- `P-POLICY`

Purpose:
- Freeze a bounded, discrete, point-source-class Track B closure target for GR01 weak-field 3D posture.
- Prevent overreach into continuum-limit or infinite-domain Green-function claims.

Non-claim boundary:
- planning-only artifact.
- non-claim control surface.
- does not promote theorem/evidence status by itself.
- no continuum-limit claim.
- no infinite-domain inversion claim.
- no full fundamental-solution uniqueness claim.
- no external truth claim.

## Track B Minimal Contract (bounded discrete posture)

Required assumption token:
- `PointSourceMappingAssumptions`

Required point-source/delta token:
- `gr01_mainstream3d_point_source_delta_posture_is_explicit`

Required bounded-domain token:
- `gr01_mainstream3d_point_source_bounded_domain_posture`

Required bounded-potential behavior token:
- `gr01_mainstream3d_point_source_bounded_potential_behavior_posture`

Required bounded 3D closure token:
- `gr01_mainstream3d_point_source_poissonEquation3D_under_bounded_delta_posture`

Required pinned partial theorem-surface token:
- `gr01_mainstream3d_point_source_partial_surface_token`

Canonical artifact pointer:
- `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean`

## Closure Thresholds

Partial theorem-surface threshold (Track B MVP):
- bounded discrete point-source contract is explicit and auditable.
- `PoissonEquation3D` closure token is pinned under explicit assumptions.
- no full Green-function inversion or asymptotic claim is implied.

Full closure threshold (not met by MVP):
- Track B is integrated with derivation-grade discharge checklist closure criteria in
  `TARGET-GR01-DERIV-CHECKLIST-PLAN`.
- any claim-promotion attempt keeps non-claim boundaries explicit and unchanged unless a new freeze cycle is approved.

## Track B Residual Discharge Target (future upgrade; not yet satisfied)

Goal:
- Upgrade Track B from assumption-only residual closure to a bounded discrete
  candidate-construction residual lemma.
- Selected future discharge path (frozen):
  - domain-wise Poisson posture away from source with an explicit center-defect witness.

Minimal discharge design inputs:
- candidate potential class:
  - define an explicit bounded-domain candidate potential profile (`Phi_candidate`)
    or a discrete Green-kernel surrogate (`G_bounded`).
- boundary condition class:
  - freeze one explicit bounded-domain boundary condition class (Dirichlet,
    Neumann, or periodic) inside the assumptions object.
  - v0 future-discharge scaffold freezes Dirichlet boundary posture as the
    initial class for residual-lemma discharge.
- candidate system object:
  - define an interior-point predicate (`IsInteriorPoint`) so boundary exclusion
    is explicit at the finite-domain system layer.
  - define a finite-domain operator object (`DirichletLinearOperator3D`) and
    RHS object (`DirichletRHS3D`) to represent operator-equation posture.
  - define an operator-equation predicate
    (`SatisfiesFiniteLinearOperatorEquationOnDomain`) and an operator-encoding
    predicate (`OperatorEncodesDiscreteLaplacianOnInterior`) for the bridge step.
  - define a finite-domain Dirichlet linear-system predicate
    (`SatisfiesDirichletLinearSystemOnDomain`) that pins boundary equations and
    interior non-source linear equations.
  - define a finite-domain Dirichlet system-satisfaction predicate
    (`SatisfiesDirichletPoissonSystemOnDomain`) that pins boundary equations and
    away-from-source interior residual equations under one auditable object.
  - define a candidate packaging record
    (`PointSourceDirichletCandidateSolution`) that carries domain, source
    posture, and system-satisfaction witness.
- stencil residual endpoint lemma:
  - prove a stencil-level lemma that the chosen candidate satisfies
    `DiscretePoissonResidual3D` point-source closure under the frozen boundary class.

Future-scoped discharge endpoint tokens (not required for MVP):
- `PointSourceDirichletBoundaryAssumptions`
- `gr01_mainstream3d_point_source_dirichlet_boundary_posture_is_explicit`
- `gr01_mainstream3d_point_source_residual_zero_away_from_source_under_dirichlet_boundary`
- `gr01_mainstream3d_point_source_center_residual_defect_is_explicit_under_dirichlet_boundary`
- `gr01_mainstream3d_point_source_residual_discharge_under_dirichlet_boundary`
- `gr01_mainstream3d_point_source_domain_residual_characterization_under_dirichlet_boundary`
- `gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_under_dirichlet_boundary`
- `FiniteDirichletDomain3D`
- `IsInteriorPoint`
- `DirichletLinearOperator3D`
- `DirichletRHS3D`
- `SatisfiesFiniteLinearOperatorEquationOnDomain`
- `OperatorEncodesDiscreteLaplacianOnInterior`
- `OperatorHasDirichletRightInverseOnDomain`
- `SatisfiesDirichletLinearSystemOnDomain`
- `SatisfiesDirichletPoissonSystemOnDomain`
- `PointSourceDirichletCandidateSolution`
- `gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_derived_from_dirichlet_system`
- `gr01_mainstream3d_point_source_system_satisfaction_from_linear_system`
- `gr01_mainstream3d_point_source_candidate_exists_from_linear_system`
- `gr01_mainstream3d_point_source_linear_system_satisfaction_from_operator_equation`
- `gr01_mainstream3d_point_source_candidate_exists_from_operator_equation`
- `gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_from_operator_equation`
- `gr01_mainstream3d_point_source_solution_exists_for_operator_equation_under_invertibility`
- `gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_exists_from_operator_equation_under_invertibility`

Discharge endpoint criteria:
- `residual_zero_under_point_source` is replaced (or discharged) by a derived
  lemma from the chosen candidate plus explicit boundary assumptions.
- first derived endpoint is expected to flow from the Dirichlet system object
  (`SatisfiesDirichletPoissonSystemOnDomain`) rather than from a direct
  residual assumption field.
- linear-system bridge endpoint is expected to prove:
  `SatisfiesDirichletLinearSystemOnDomain -> SatisfiesDirichletPoissonSystemOnDomain`
  via `gr01_mainstream3d_point_source_system_satisfaction_from_linear_system`.
- operator-equation bridge endpoint is expected to prove:
  `SatisfiesFiniteLinearOperatorEquationOnDomain -> SatisfiesDirichletLinearSystemOnDomain`
  under `OperatorEncodesDiscreteLaplacianOnInterior` via
  `gr01_mainstream3d_point_source_linear_system_satisfaction_from_operator_equation`.
- candidate packaging endpoint is expected to prove:
  linear-system satisfaction plus explicit source/domain/delta assumptions imply
  `∃ hCandidate : PointSourceDirichletCandidateSolution` via
  `gr01_mainstream3d_point_source_candidate_exists_from_linear_system`.
- operator-to-candidate composition endpoint is expected to prove:
  operator-equation posture plus explicit source/domain/delta assumptions imply
  `∃ hCandidate : PointSourceDirichletCandidateSolution` via
  `gr01_mainstream3d_point_source_candidate_exists_from_operator_equation`.
- operator-to-derived-away-from-source endpoint is expected to prove:
  operator-equation posture plus explicit boundary/encoding assumptions imply
  `PoissonEquation3DAwayFromSourceOnDomain` via
  `gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_from_operator_equation`.
- solver-grade existence endpoint is expected to prove:
  invertibility witness posture (right inverse on interior + boundary-zero witness)
  implies `∃ Φ` satisfying boundary posture and
  `SatisfiesFiniteLinearOperatorEquationOnDomain` via
  `gr01_mainstream3d_point_source_solution_exists_for_operator_equation_under_invertibility`.
- solver-grade existential closure endpoint is expected to prove:
  invertibility witness posture plus operator-encoding assumptions imply
  `∃ Φ, PoissonEquation3DAwayFromSourceOnDomain Φ ρ κ domain sourceCenter`
  via
  `gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_exists_from_operator_equation_under_invertibility`.
- no continuum-limit claim, infinite-domain inversion claim, or uniqueness claim
  is introduced by this discharge step.

## Dependencies

- `formal/docs/paper/DERIVATION_TARGET_GR01_3D_MAINSTREAM_CLASS_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_GR01_DERIVATION_GRADE_CHECKLIST_v0.md`
- `formal/docs/paper/TOE_GR01_THEOREM_SURFACE_v0.md`
- `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md`

## Freeze Policy

- This target is Track B-specific and does not supersede Track A by itself.
- This target does not alter roadmap unlock ordering.
- `TOE-GR-3D-03` remains `B-BLOCKED` until closure criteria are met under explicit non-claim boundaries.
