# TOE-GR-01 Projection Bridge Spec v0

Spec ID:
- `TOE_GR01_PROJECTION_BRIDGE_SPEC_v0`

Purpose:
- Define the explicit projection bridge obligations that replace monolithic `hProjectionFromCore`.
- Make bridge assumptions auditable and classifiable (`P-POLICY` vs `B-BLOCKED` vs `T-CONDITIONAL`).

Canonical Lean surface:
- `formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean`

Bridge decomposition (v0):
1. `ProjectionMapWellFormed`
- Inputs: `PotentialIdentification`, `SourceIdentification`.
- Role: certifies potential/source projection carriers are explicitly selected and well-formed.
- Classification plan: `T-CONDITIONAL` via symmetry-promotion theorem chain in
  `formal/toe_formal/ToeFormal/Variational/GR01SymmetryPromotion.lean`
  (`gr01_projection_map_well_formed`).

2. `WeakFieldTruncationSound`
- Inputs: `WeakFieldAnsatz`, `SmallPerturbationExpansion`.
- Role: captures weak-field first-order truncation posture and remainder-bounded assumption.
- Classification plan: approximation discharge is `T-CONDITIONAL` via
  `formal/toe_formal/ToeFormal/Variational/GR01ScalingPromotion.lean`
  (`gr01_first_order_truncation_sound`), while the theorem-surface bridge component
  remains explicit.

3. `OperatorToDiscreteResidual` (transport lemma)
- Inputs: extracted-operator residual equation plus `h_extracted_is_discrete`.
- Role: rewrites operator-form residual into `DiscretePoissonResidual1D`.
- Classification plan: `T-CONDITIONAL` target (pure discrete/operator transport surface).
- 3D posture token:
  - `DiscretePoissonResidual3D` remains a declared reporting target for dimensional upgrade without theorem promotion in this spec.
- 3D mapping assumptions + conditional lift:
  - `Lift1DTo3DMappingAssumptions`
  - `discretePoissonResidual3D_of_lift_x_only`
  - `poissonEquation3D_of_poissonEquation1D_under_lift_x_only`
- improved 3D mapping assumptions + conditional lift:
  - `Separable3DMappingAssumptions`
  - `discretePoissonResidual3D_of_separable`
  - `poissonEquation3D_of_componentwise_poissonEquation1D_under_separable`
- mainstream-class 3D closure gate (blocker-facing):
  - `TOE-GR-3D-03`
  - `TARGET-GR01-3D-03-PLAN`
  - `formal/docs/paper/DERIVATION_TARGET_GR01_3D_MAINSTREAM_CLASS_v0.md`
  - Track A spherical partial theorem-surface tokens:
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
    - `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DSpherical.lean`
  - Track A reduction status:
    - `laplacian_reduces_to_radial` is currently carried as a contract assumption field;
      a stencil-derived discharge lemma is future-scoped.
    - Path 2 bridge requirement:
      - Track A green-class token must be derived from 3D operator-equation posture
        (`operator_equation_3d_away_from_source`) and not by directly assuming
        radial away-from-source residual closure.
      - Track A bridge is bounded mapping transport (3D away-from-source operator
        posture -> bounded radial away-from-source closure), not an upstream
        action-to-operator derivation discharge.
      - upstream action-to-operator discharge is tracked by:
        - `TARGET-GR01-ACTION-TO-OPERATOR-DISCRETE-DERIVATION_v0`
        - `formal/docs/paper/DERIVATION_TARGET_GR01_ACTION_TO_OPERATOR_DISCRETE_DERIVATION_v0.md`
  - Track B point-source partial theorem-surface tokens:
    - `TARGET-GR01-3D-POINT-SOURCE-PLAN`
    - `PointSourceMappingAssumptions`
    - `gr01_mainstream3d_point_source_delta_posture_is_explicit`
    - `gr01_mainstream3d_point_source_bounded_domain_posture`
    - `gr01_mainstream3d_point_source_bounded_potential_behavior_posture`
    - `gr01_mainstream3d_point_source_poissonEquation3D_under_bounded_delta_posture`
    - `gr01_mainstream3d_point_source_partial_surface_token`
    - `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean`
    - `formal/docs/paper/DERIVATION_TARGET_GR01_3D_POINT_SOURCE_CLASS_v0.md`
  - Track B reduction status:
    - bounded-domain point-source closure is currently encoded as an assumption-scoped contract;
      no continuum-limit or infinite-domain Green inversion is claimed.
    - future-scoped endpoint token (not required for v0 MVP):
      `gr01_mainstream3d_point_source_residual_discharge_under_dirichlet_boundary`.
    - future-scoped center-defect witness token (not required for v0 MVP):
      `gr01_mainstream3d_point_source_center_residual_defect_is_explicit_under_dirichlet_boundary`.
    - future-scoped domain-wise bridge token (not required for v0 MVP):
      `gr01_mainstream3d_point_source_domain_residual_characterization_under_dirichlet_boundary`.
    - future-scoped away-from-source Poisson posture token (not required for v0 MVP):
      `gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_under_dirichlet_boundary`.
    - future-scoped finite-domain system/candidate objects (not required for v0 MVP):
      `FiniteDirichletDomain3D`,
      `IsInteriorPoint`,
      `DirichletLinearOperator3D`,
      `DirichletRHS3D`,
      `SatisfiesFiniteLinearOperatorEquationOnDomain`,
      `OperatorEncodesDiscreteLaplacianOnInterior`,
      `OperatorHasDirichletRightInverseOnDomain`,
      `SatisfiesDirichletLinearSystemOnDomain`,
      `SatisfiesDirichletPoissonSystemOnDomain`,
      `PointSourceDirichletCandidateSolution`.
    - future-scoped operator-equation-to-linear-system bridge token (not required for v0 MVP):
      `gr01_mainstream3d_point_source_linear_system_satisfaction_from_operator_equation`.
    - future-scoped first derived-from-system bridge token (not required for v0 MVP):
      `gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_derived_from_dirichlet_system`.
    - future-scoped linear-system-to-system bridge token (not required for v0 MVP):
      `gr01_mainstream3d_point_source_system_satisfaction_from_linear_system`.
    - future-scoped candidate-packaging token (not required for v0 MVP):
      `gr01_mainstream3d_point_source_candidate_exists_from_linear_system`.
    - future-scoped operator-to-candidate composition token (not required for v0 MVP):
      `gr01_mainstream3d_point_source_candidate_exists_from_operator_equation`.
    - future-scoped operator-to-derived-away-from-source token (not required for v0 MVP):
      `gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_from_operator_equation`.
    - future-scoped solver-grade existence token (not required for v0 MVP):
      `gr01_mainstream3d_point_source_solution_exists_for_operator_equation_under_invertibility`.
    - future-scoped solver-grade existential away-from-source token (not required for v0 MVP):
      `gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_exists_from_operator_equation_under_invertibility`.

4. `ELImpliesDiscretePoissonResidual` (modeling lemma)
- Inputs: projected potential/source/operator/calibration objects.
- Required implication:
  - `EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32`
  - implies discrete Poisson residual equation:
    - `DiscretePoissonResidual1D Phi rho kappa = 0` (pointwise).
- Classification plan: `T-CONDITIONAL` via bridge-promotion theorem chain in
  `formal/toe_formal/ToeFormal/Variational/GR01BridgePromotion.lean`
  (`gr01_discrete_residual_from_bridge_promotion_chain`).

5. Dominant remaining blocker (v0)
- Weak-field policy blocker list is empty at the assumption-registry level.
- Bridge promotion status for `ASM-GR01-APP-02` is closed as `T-CONDITIONAL`.
- End-to-end theorem-chain closure milestone is complete (`TOE-GR-CLS-01`):
  - `formal/docs/paper/DERIVATION_TARGET_GR01_END_TO_END_CLOSURE_v0.md`
  - `formal/toe_formal/ToeFormal/Variational/GR01EndToEndClosure.lean`
- Remaining blocker is derivation-grade analytic discharge package closure:
  - `formal/docs/paper/DERIVATION_TARGET_GR01_DERIVATION_GRADE_CHECKLIST_v0.md`
- Action/RAC stance is explicitly frozen as conditional:
  - `formal/docs/paper/TOE_GR01_ACTION_RAC_STANCE_v0.md`

Constructible bridge object (v0):
- Constructor: `mkWeakFieldProjectionFromCore`.
- Signature intent:
  - `(ProjectionMapWellFormed, WeakFieldTruncationSound, ELImpliesDiscretePoissonResidual) -> WeakFieldProjectionFromCore`.
- Governance meaning:
  - projection bridge is no longer a single opaque theorem input;
  - obligations are explicit and separately classifiable.
  - canonical theorem path does not accept `ELImpliesProjectedResidual`.

Output surface:
- Main theorem remains:
  - `TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions`
- 3D reporting posture token:
  - `PoissonEquation3D` (`nabla_3D^2 Phi = kappa * rho`) is declared but not discharged here.
- Theorem now consumes bridge components and internally constructs `WeakFieldProjectionFromCore`.

Non-claim:
- This spec does not claim full GR recovery.
- This spec does not by itself close end-to-end GR01 derivation-grade criteria.
