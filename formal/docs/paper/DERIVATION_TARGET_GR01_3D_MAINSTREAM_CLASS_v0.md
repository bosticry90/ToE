# Derivation Target: GR01 3D Mainstream-Class Closure v0

Spec ID:
- `DERIVATION_TARGET_GR01_3D_MAINSTREAM_CLASS_v0`

Target ID:
- `TARGET-GR01-3D-03-PLAN`

Classification:
- `P-POLICY`

Purpose:
- Freeze a blocker-facing 3D mainstream-class target for GR01 weak-field closure.
- Prevent premature GR pillar closure based only on embedding/separable transport milestones.

Non-claim boundary:
- planning-only artifact.
- non-claim control surface.
- does not promote theorem/evidence status by itself.
- no comparator-lane authorization.
- no full GR/EFE recovery claim.
- no external truth claim.

## Mainstream-Class 3D Closure Options (at least one required before GR closure)

1. Spherical symmetry track:
- Explicit spherical-symmetry assumptions over `Phi` and `rho`.
- Bounded reduction from 3D operator posture to radial closure statement.
- Conditional theorem token for spherical-class residual closure.

2. Discrete Green-function / point-source track:
- Explicit source-class assumptions (delta-like source posture).
- Bounded existence/behavior statement for 3D potential profile.
- Conditional theorem token for point-source-class closure posture.

## MVP Discharge Criteria (Track-scoped)

Selected execution posture (v0):
- Track A remains pinned as a contract-level partial theorem-surface baseline.
- Track B (point-source class) is now pinned as the next mainstream execution route for strengthened 3D physical alignment.

## Path 2 Closure Sprint (Track A first; bounded/discrete)

Path 2 sprint constraint:
- keep `PILLAR-GR` as the only `ACTIVE` pillar.
- do not unlock `PILLAR-QM`, `PILLAR-EM`, or `PILLAR-SR` while:
  - `TOE-GR-3D-03` remains blocker-facing, or
  - action/RAC alignment adjudication remains `NOT_YET_DISCHARGED`.

Track A minimal closure-token set for Path 2:
- `gr01_mainstream3d_discrete_laplacian_reduces_to_radial_under_spherical_symmetry`
- `gr01_mainstream3d_radial_poisson_away_from_source_from_operator_equation_under_spherical_symmetry`
- `gr01_mainstream3d_point_source_model_discrete_delta_or_shell`
- `gr01_mainstream3d_green_class_partial_surface_token`
- `SphericalOperatorEquationAwayFromSourceAssumptions`
- `operator_equation_3d_away_from_source`
- `radiusBound`
- `radial_index_realized_within_bound`

Path 2 closure interpretation:
- these Track A tokens are required closure-evidence surfaces for adjudication.
- Track A green-class token must be derived from 3D operator-equation posture, not
  by directly assuming radial away-from-source residual closure as a field.
- `operator_equation_3d_away_from_source` is currently treated as bounded 3D
  away-from-source Poisson-operator posture; Track A contributes a mapping bridge
  from that 3D posture to bounded radial away-from-source closure.
- this Path 2 Track A bridge is not, by itself, an upstream action-to-operator
  derivation discharge.
- upstream action-to-operator discharge is tracked separately by:
  - `TARGET-GR01-ACTION-TO-OPERATOR-DISCRETE-DERIVATION_v0`
  - `formal/docs/paper/DERIVATION_TARGET_GR01_ACTION_TO_OPERATOR_DISCRETE_DERIVATION_v0.md`
- no continuum-limit claim, no infinite-domain inversion claim, no uniqueness claim.

Track A (spherical symmetry) MVP discharge criteria:
- Required assumption token:
  - `SphericalSymmetryMappingAssumptions`
- Contract-level boundary (explicit):
  - `laplacian_reduces_to_radial` is currently an assumption field inside
    `SphericalSymmetryMappingAssumptions`, not a derived stencil-level lemma.
  - Track A remains a partial theorem-surface contract until that reduction is discharged.
- Required bounded reduction token:
  - `gr01_mainstream3d_discrete_laplacian_reduces_to_radial_under_spherical_symmetry`
- Required residual reduction token:
  - `gr01_mainstream3d_discrete_residual_reduces_to_radial_under_spherical_symmetry`
- Required transport theorem token:
  - `gr01_mainstream3d_poissonEquation3D_of_radial_poisson_under_spherical_symmetry`
- Required pinned partial theorem-surface token:
  - `gr01_mainstream3d_spherical_partial_surface_token`
- Canonical artifact pointer:
  - `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DSpherical.lean`
- Partial theorem-surface threshold:
  - assumptions are explicit and bounded,
  - radial-to-3D transport theorem is pinned and references `PoissonEquation3D`,
  - no Green-function claim is implied.
- Full closure threshold (not met by MVP):
  - spherical track is connected to full analytic discharge package criteria in
    `TARGET-GR01-DERIV-CHECKLIST-PLAN`,
  - closure wording can be promoted without changing non-claim boundaries.

## Track A Reduction Discharge Target (future upgrade; not yet satisfied)

Goal:
- Replace the contract-level reduction field `laplacian_reduces_to_radial`
  with a derived lemma under explicit lattice symmetry predicates.

Minimal discharge design inputs:
- Explicit `radialIndex` semantics:
  - define the intended lattice radius index contract and admissible domain.
- Explicit spherical symmetry predicate:
  - define when `Phi`/`rho` are radial with respect to `radialIndex`.
- Explicit radial operator intent:
  - fix the radial operator that is intended to match the 3D stencil under symmetry.

Discharge endpoint criteria:
- A derived theorem (not an assumption field) proves the 3D-to-radial reduction
  under the explicit symmetry predicate and stated domain assumptions.
- Track A can then be evaluated for promotion beyond partial theorem-surface posture
  without changing non-claim boundaries.

Track B (discrete Green-function / point-source) MVP discharge criteria:
- Required assumption class:
  - explicit point-source/delta-like source posture.
- Required bounded behavior statement:
  - bounded-domain existence/behavior theorem surface for 3D potential profile.
- Required assumption token:
  - `PointSourceMappingAssumptions`
- Required point-source/delta token:
  - `gr01_mainstream3d_point_source_delta_posture_is_explicit`
- Required bounded-domain token:
  - `gr01_mainstream3d_point_source_bounded_domain_posture`
- Required bounded-potential behavior token:
  - `gr01_mainstream3d_point_source_bounded_potential_behavior_posture`
- Required bounded 3D closure token:
  - `gr01_mainstream3d_point_source_poissonEquation3D_under_bounded_delta_posture`
- Required pinned partial theorem-surface token:
  - `gr01_mainstream3d_point_source_partial_surface_token`
- Canonical artifact pointers:
  - Track B frozen target ID: `TARGET-GR01-3D-POINT-SOURCE-PLAN`
  - `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean`
  - `formal/docs/paper/DERIVATION_TARGET_GR01_3D_POINT_SOURCE_CLASS_v0.md`
- Contract-level boundary (explicit):
  - Track B is bounded discrete posture only and is currently assumption-scoped.
  - no continuum-limit or infinite-domain Green-function inversion claim is implied.
- Partial theorem-surface threshold:
  - point-source assumptions and bounded behavior are explicit and auditable.
- Full closure threshold (not met by MVP):
  - integration with derivation-grade discharge checklist under unchanged scope.
  - Track B future discharge endpoint token is frozen in the Track B target doc:
    `gr01_mainstream3d_point_source_residual_discharge_under_dirichlet_boundary`.
  - Track B future center-defect witness token is frozen in the Track B target doc:
    `gr01_mainstream3d_point_source_center_residual_defect_is_explicit_under_dirichlet_boundary`.
  - Track B future domain-wise residual bridge token is frozen in the Track B target doc:
    `gr01_mainstream3d_point_source_domain_residual_characterization_under_dirichlet_boundary`.
  - Track B future away-from-source Poisson posture token is frozen in the Track B target doc:
    `gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_under_dirichlet_boundary`.
  - Track B future finite-domain system/candidate objects are frozen in the Track B target doc:
    `FiniteDirichletDomain3D`, `IsInteriorPoint`,
    `DirichletLinearOperator3D`, `DirichletRHS3D`,
    `SatisfiesFiniteLinearOperatorEquationOnDomain`,
    `OperatorEncodesDiscreteLaplacianOnInterior`,
    `OperatorHasDirichletRightInverseOnDomain`,
    `SatisfiesDirichletLinearSystemOnDomain`,
    `SatisfiesDirichletPoissonSystemOnDomain`,
    `PointSourceDirichletCandidateSolution`.
  - Track B future operator-equation-to-linear-system bridge token is frozen in the Track B target doc:
    `gr01_mainstream3d_point_source_linear_system_satisfaction_from_operator_equation`.
  - Track B future derived-from-system away-from-source token is frozen in the Track B target doc:
    `gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_derived_from_dirichlet_system`.
  - Track B future linear-system-to-system bridge token is frozen in the Track B target doc:
    `gr01_mainstream3d_point_source_system_satisfaction_from_linear_system`.
  - Track B future candidate-packaging token is frozen in the Track B target doc:
    `gr01_mainstream3d_point_source_candidate_exists_from_linear_system`.
  - Track B future operator-to-candidate composition token is frozen in the Track B target doc:
    `gr01_mainstream3d_point_source_candidate_exists_from_operator_equation`.
  - Track B future operator-to-derived-away-from-source token is frozen in the Track B target doc:
    `gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_from_operator_equation`.
  - Track B future solver-grade existence token is frozen in the Track B target doc:
    `gr01_mainstream3d_point_source_solution_exists_for_operator_equation_under_invertibility`.
  - Track B future solver-grade existential away-from-source closure token is frozen in the Track B target doc:
    `gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_exists_from_operator_equation_under_invertibility`.

## Discharge-Attempt Package Target (execution pressure while blocked)

- Required attempt-package target:
  - `TARGET-GR01-3D-03-ATTEMPT-PACKAGE-PLAN`
- Canonical attempt-package artifact:
  - `formal/docs/paper/DERIVATION_TARGET_GR01_3D_03_DISCHARGE_ATTEMPT_PACKAGE_v0.md`
- Required attempt-package posture:
  - attempt deliverables are explicit,
  - mandatory failure triggers are explicit,
  - objective token remains pinned in the Track B scaffold module.

## Closure-Focused Package Target (transition criteria while blocked)

- Required closure-package target:
  - `TARGET-GR01-3D-03-CLOSURE-PACKAGE-PLAN`
- Canonical closure-package artifact:
  - `formal/docs/paper/DERIVATION_TARGET_GR01_3D_03_CLOSURE_PACKAGE_v0.md`
- Required closure-package posture:
  - closure-transition rule is explicit,
  - required closure tokens for Track B are explicit,
  - closure adjudication note is explicit before status change.

## Closure Gate Token

- Result-row token: `TOE-GR-3D-03`
- Status intent (v0): bounded/discrete closure adjudication is frozen as
  `T-CONDITIONAL` with `ADJUDICATION: SATISFIED_v0_DISCRETE` under explicit
  non-claim boundaries.

## Dependencies

- `formal/docs/paper/DERIVATION_TARGET_NEWTONIAN_LIMIT_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_GR01_DERIVATION_GRADE_CHECKLIST_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_GR01_3D_POINT_SOURCE_CLASS_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_GR01_3D_03_DISCHARGE_ATTEMPT_PACKAGE_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_GR01_3D_03_CLOSURE_PACKAGE_v0.md`
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `formal/docs/paper/TOE_GR01_THEOREM_SURFACE_v0.md`

## Freeze Policy

- This target does not alter existing theorem labels.
- This target does not unlock SR/EM.
- GR closure remains blocked until this target has at least a planning pointer plus pinned partial theorem-surface token.
- `TOE-GR-3D-03` remains `T-CONDITIONAL` under bounded/discrete v0 scope with
  non-claim boundaries retained.
- Upstream depth discharge is delegated to
  `TARGET-GR01-ACTION-TO-OPERATOR-DISCRETE-DERIVATION_v0`.
