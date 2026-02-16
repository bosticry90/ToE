# TOE-GR-01 Theorem Surface v0

Spec ID:
- `TOE_GR01_THEOREM_SURFACE_v0`

Purpose:
- Define a paper-facing theorem surface for the first true derivation target (`TOE-GR-01`).
- Keep the theorem surface explicit and assumption-scoped while analytic discharge remains in progress.

Canonical theorem surface:
- Module: `formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean`
- Theorem: `TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions`

Statement posture:
- The theorem surface is structural-only in v0.
- It explicitly lists:
  - default-quotient variational assumptions (`ε`, `hε`, `hAction`, `hRAC`),
  - weak-field derivation assumptions (`hWeakFieldAnsatz`, `hSmallPerturbationExpansion`,
    `hPotentialIdentification`, `hSourceIdentification`, `hLaplacianExtraction`,
    `hUnitsAndCalibration`),
  - projection bridge components:
    - `hProjectionMapWellFormed`
    - `hWeakFieldTruncationSound`
    - `hELImpliesDiscretePoissonResidual`,
  - target statement surface (`WeakFieldPoissonLimitStatement`).

Non-vacuity rule (v0):
- `PoissonEquation1D` is defined as a concrete residual-equality predicate on a discrete 1D Laplacian.
- `PoissonEquation3D` is declared as a physics-posture target predicate on a discrete 3D Laplacian.
- `WeakFieldPoissonLimitStatement` is not encoded as `exists ... , True`.
- The theorem does not accept `hPoissonLimit` as an input.

3D posture (bounded, non-promotional):
- 3D reporting target equation:
  - `nabla_3D^2 Phi = kappa * rho`
- Lean posture tokens:
  - `DiscreteLaplacian3D`
  - `DiscretePoissonResidual3D`
  - `PoissonEquation3D`
- Embedding-example mapping assumptions (explicit, conditional):
  - `Lift1DTo3DMappingAssumptions`
  - `potential_lift_x_only`
  - `source_lift_x_only`
- Derived embedding-example 3D residual transport theorems (conditional):
  - `discreteLaplacian3D_of_lift_x_only`
  - `discretePoissonResidual3D_of_lift_x_only`
  - `poissonEquation3D_of_poissonEquation1D_under_lift_x_only`
  - `weakFieldPoissonLimitStatement3D_of_weakFieldPoissonLimitStatement_under_lift_x_only`
- Separable-3D mapping assumptions (explicit, conditional):
  - `Separable3DMappingAssumptions`
  - `potential_is_separable`
  - `source_is_separable`
- Derived separable-3D residual transport theorems (conditional):
  - `discreteLaplacian3D_of_separable`
  - `discretePoissonResidual3D_of_separable`
  - `poissonEquation3D_of_componentwise_poissonEquation1D_under_separable`
  - `weakFieldPoissonLimitStatement3D_of_componentwise_poissonEquation1D_under_separable`
- This posture does not claim 3D derivation discharge is complete in v0.
- Canonical 3D milestones:
  - `TOE-GR-3D-01`: x-only embedding example.
  - `TOE-GR-3D-02`: improved separable 3D mapping theorem-conditional milestone.
  - `TOE-GR-3D-03`: mainstream-class 3D closure gate milestone (spherical/Green-class target; blocker-facing).
- Track A (spherical) pinned partial theorem-surface tokens:
  - `SphericalSymmetryMappingAssumptions`
  - `gr01_mainstream3d_discrete_laplacian_reduces_to_radial_under_spherical_symmetry`
  - `gr01_mainstream3d_discrete_residual_reduces_to_radial_under_spherical_symmetry`
  - `gr01_mainstream3d_radial_poisson_away_from_source_from_operator_equation_under_spherical_symmetry`
  - `gr01_mainstream3d_point_source_model_discrete_delta_or_shell`
  - `gr01_mainstream3d_green_class_partial_surface_token`
  - `SphericalOperatorEquationAwayFromSourceAssumptions`
  - `operator_equation_3d_away_from_source`
  - `radiusBound`
  - `radial_index_realized_within_bound`
  - `gr01_mainstream3d_poissonEquation3D_of_radial_poisson_under_spherical_symmetry`
  - `gr01_mainstream3d_spherical_partial_surface_token`
  - canonical artifact pointer:
    - `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DSpherical.lean`
  - contract-level boundary:
    - Track A currently treats 3D Laplacian-to-radial reduction as an explicit
      mapping-assumption field (`laplacian_reduces_to_radial`), not a derived stencil theorem.
    - Path 2 bridge requirement: Track A green-class token is derived from
      3D operator-equation posture (`operator_equation_3d_away_from_source`)
      and not by directly assuming radial residual closure.
    - Track A bridge scope: bounded mapping transport from 3D away-from-source
      operator posture to bounded radial away-from-source closure; this does not
      by itself discharge an upstream action-to-operator derivation.
    - upstream action-to-operator discharge is tracked by:
      - `TARGET-GR01-ACTION-TO-OPERATOR-DISCRETE-DERIVATION_v0`
      - `formal/docs/paper/DERIVATION_TARGET_GR01_ACTION_TO_OPERATOR_DISCRETE_DERIVATION_v0.md`
- Track B (point-source) pinned partial theorem-surface tokens:
  - `TARGET-GR01-3D-POINT-SOURCE-PLAN`
  - `PointSourceMappingAssumptions`
  - `gr01_mainstream3d_point_source_delta_posture_is_explicit`
  - `gr01_mainstream3d_point_source_bounded_domain_posture`
  - `gr01_mainstream3d_point_source_bounded_potential_behavior_posture`
  - `gr01_mainstream3d_point_source_poissonEquation3D_under_bounded_delta_posture`
  - `gr01_mainstream3d_point_source_partial_surface_token`
  - canonical artifact pointer:
    - `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean`
  - contract-level boundary:
    - Track B currently encodes bounded-domain point-source closure as an explicit
      assumption-scoped contract and does not claim continuum Green-function inversion.
  - future-scoped discharge endpoint token (not required for v0 MVP):
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
    - `gr01_mainstream3d_point_source_residual_discharge_under_dirichlet_boundary`
    - `gr01_mainstream3d_point_source_center_residual_defect_is_explicit_under_dirichlet_boundary`
    - `gr01_mainstream3d_point_source_domain_residual_characterization_under_dirichlet_boundary`
    - `gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_under_dirichlet_boundary`
    - `gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_derived_from_dirichlet_system`
    - `gr01_mainstream3d_point_source_system_satisfaction_from_linear_system`
    - `gr01_mainstream3d_point_source_candidate_exists_from_linear_system`
    - `gr01_mainstream3d_point_source_linear_system_satisfaction_from_operator_equation`
    - `gr01_mainstream3d_point_source_candidate_exists_from_operator_equation`
    - `gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_from_operator_equation`
    - `gr01_mainstream3d_point_source_solution_exists_for_operator_equation_under_invertibility`
    - `gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_exists_from_operator_equation_under_invertibility`

Current status:
- `B-BLOCKED` for analytic derivation discharge.
- This artifact is a non-vacuous theorem-shape contract, not yet an analytic proof of Poisson emergence.
- Bridge decomposition is explicit in Lean helper lemmas:
  - `OperatorToDiscreteResidual`
  - `mkWeakFieldProjectionFromCore`
  - `weakFieldResidualFromProjection`
  - `weakFieldPoissonResidualOfProjection`
- End-to-end closure theorem-chain surface:
  - `formal/toe_formal/ToeFormal/Variational/GR01EndToEndClosure.lean`
  - `gr01_end_to_end_chain_bundle_under_promoted_assumptions`
  - `gr01_end_to_end_poisson_equation_under_promoted_assumptions`
- Dominant blocker (v1): derivation-grade analytic discharge package closure
  (scaffold-to-discharge upgrades + analytic report alignment) remains open.
- Action/RAC alignment posture is frozen separately:
  - `formal/docs/paper/TOE_GR01_ACTION_RAC_STANCE_v0.md`

Non-claim:
- No GR/EFE recovery claim.
- No external truth claim.
