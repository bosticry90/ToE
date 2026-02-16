# TOE-GR-01 Laplacian Extraction v0

Spec ID:
- `TOE_GR01_LAPLACIAN_EXTRACTION_v0`

Purpose:
- Fix the operator-reduction path that extracts Poisson-form structure from the weak-field equation surface.
- Keep operator simplification assumptions explicit and auditable.

## Assumption Freeze And Inputs

Assumption IDs:
- `ASM-GR01-STR-01`: operator/discrete transport lemma posture.
- `ASM-GR01-APP-02`: EL-to-discrete residual bridge token.
- `ASM-GR01-APP-04`: operator-residual bridge under weak-field bound.
- `ASM-GR01-BND-01`: boundary/discrete-domain conventions.

Canonical pointers:
- `formal/docs/paper/ASSUMPTION_REGISTRY_v1.md`
- `formal/docs/paper/TOE_GR01_PROJECTION_BRIDGE_SPEC_v0.md`
- `formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean`

## Operator Extraction Scaffold (v0)

1. Start from weak-field leading-order equation surface.
2. Apply scalar-potential identification from `TOE_GR01_POTENTIAL_IDENTIFICATION_v0.md`.
3. Reduce retained operator terms to Laplacian structure on `Phi`.
4. Assemble leading-order balance:
   - `nabla^2 Phi = kappa * rho` (bounded weak-field scope).
5. Track dropped-term class and bounded remainder assumptions.

## 3D Posture Token (Reporting Scope)

- Canonical discrete theorem predicate remains `PoissonEquation1D` for current chain closure.
- Physics-facing posture now includes explicit 3D target equation shape:
  - `nabla_3D^2 Phi = kappa * rho`.
- 3D operator and residual reporting tokens are pinned in Lean as:
  - `DiscreteLaplacian3D`
  - `DiscretePoissonResidual3D`
  - `PoissonEquation3D`
- This is a posture upgrade, not a claim that 3D derivation discharge is complete.

## 3D Mapping Assumptions And Derived Statements (Conditional)

- Embedding-example assumptions are explicit and witness-carrying:
  - `Lift1DTo3DMappingAssumptions`
  - `potential_lift_x_only`
  - `source_lift_x_only`
- Derived embedding transport chain in Lean:
  - `discreteLaplacian3D_of_lift_x_only`
  - `discretePoissonResidual3D_of_lift_x_only`
  - `poissonEquation3D_of_poissonEquation1D_under_lift_x_only`
- Interpretation (embedding example):
  - this is a bounded conditional lift from 1D theorem residual to 3D residual under explicit x-only lift assumptions.

- Separable-3D assumptions are explicit and witness-carrying:
  - `Separable3DMappingAssumptions`
  - `potential_is_separable`
  - `source_is_separable`
- Derived separable transport chain in Lean:
  - `discreteLaplacian3D_of_separable`
  - `discretePoissonResidual3D_of_separable`
  - `poissonEquation3D_of_componentwise_poissonEquation1D_under_separable`
- Interpretation (improved 3D target):
  - this is a bounded conditional 3D reduction beyond x-only embedding; full spherical/Green-function closure remains future-scoped.

- Mainstream Track A spherical assumptions are explicit and bounded:
  - `SphericalSymmetryMappingAssumptions`
  - `radial_shell_bound`
- Derived spherical partial theorem-surface chain in Lean:
  - `gr01_mainstream3d_discrete_laplacian_reduces_to_radial_under_spherical_symmetry`
  - `gr01_mainstream3d_discrete_residual_reduces_to_radial_under_spherical_symmetry`
  - `gr01_mainstream3d_poissonEquation3D_of_radial_poisson_under_spherical_symmetry`
  - `gr01_mainstream3d_spherical_partial_surface_token`
- Canonical Track A artifact pointer:
  - `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DSpherical.lean`

- Mainstream Track B point-source assumptions are explicit and bounded:
  - `TARGET-GR01-3D-POINT-SOURCE-PLAN`
  - `PointSourceMappingAssumptions`
  - `delta_posture`
  - `bounded_domain`
- Derived point-source partial theorem-surface chain in Lean:
  - `gr01_mainstream3d_point_source_delta_posture_is_explicit`
  - `gr01_mainstream3d_point_source_bounded_domain_posture`
  - `gr01_mainstream3d_point_source_bounded_potential_behavior_posture`
  - `gr01_mainstream3d_point_source_poissonEquation3D_under_bounded_delta_posture`
  - `gr01_mainstream3d_point_source_partial_surface_token`
- Canonical Track B artifact pointers:
  - `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean`
  - `formal/docs/paper/DERIVATION_TARGET_GR01_3D_POINT_SOURCE_CLASS_v0.md`

## Units And Operator Mapping

- Laplacian operator role:
  - spatial second-derivative balance operator on potential field.
- `kappa * rho` role:
  - source coupling term under weak-field scaling.
- Units consistency requirement:
  - operator side and source side must remain dimensionally consistent under the `TOE_GR01_KAPPA_CALIBRATION_v0.md` posture.

Required explicit assumptions:
- weak-field truncation validity,
- domain/boundary conditions,
- gauge compatibility,
- source regularity and operator-domain admissibility.

Dependencies:
- theorem surface: `formal/docs/paper/TOE_GR01_THEOREM_SURFACE_v0.md`
- weak-field expansion note: `formal/docs/paper/TOE_GR01_WEAK_FIELD_EXPANSION_NOTE_v0.md`
- potential map: `formal/docs/paper/TOE_GR01_POTENTIAL_IDENTIFICATION_v0.md`

## DER-01 Theorem-Surface Linkage (v0)

- Canonical scaffold-bundle theorem token:
  - `gr01_der01_scaffold_bundle_under_promoted_assumptions`
  - module: `formal/toe_formal/ToeFormal/Variational/GR01DerivationScaffoldPromotion.lean`
- Laplacian-extraction closure remains assumption-scoped and participates in the
  scaffold bundle via `FirstOrderRemainderSuppressed`.

Non-claim:
- This v0 artifact is an extraction blueprint, not a completed analytic proof.

## Failure Modes And Falsifiability Hooks

- If operator extraction depends on undocumented gauge/boundary choices, the derivation path fails audit.
- If 1D and 3D operator postures are conflated without explicit mapping assumptions, claims remain blocked.
- If dimensional consistency between `nabla^2 Phi` and `kappa * rho` cannot be maintained, closure remains blocked.
