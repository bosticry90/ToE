# TOE-GR-01 Analytic Discharge v0

Spec ID:
- `TOE_GR01_ANALYTIC_DISCHARGE_v0`

Classification:
- `T-CONDITIONAL`

Purpose:
- Provide one explicit analytic derivation narrative for GR01 in weak-field scope.
- Freeze approximation regime and scaling hierarchy in paper-facing form.
- Make remaining blockers explicit and auditable.

Non-claim boundary:
- This artifact does not claim full GR field-equation recovery.
- This artifact does not claim external truth.
- This artifact does not promote blocked assumptions by itself.

## Assumption Freeze (with IDs)

Registry pointer:
- `formal/docs/paper/ASSUMPTION_REGISTRY_v1.md`
- `formal/docs/paper/DERIVATION_TARGET_GR01_BRIDGE_PROMOTION_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_GR01_SCALING_PROMOTION_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_GR01_SYMMETRY_PROMOTION_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_GR01_END_TO_END_CLOSURE_v0.md`

Frozen assumptions used here:
- `ASM-GR01-STR-01`: transport lemma `OperatorToDiscreteResidual` (theorem-level bookkeeping).
- `ASM-GR01-REG-01`: weak-field regime predicate theorem-conditional status (`WeakFieldRegimePredicate`).
- `ASM-GR01-APP-01`: first-order weak-field scaling/truncation theorem-conditional status via scaling-promotion chain.
- `ASM-GR01-SYM-01`: projection-map well-formedness theorem-conditional status via symmetry-promotion chain.
- `ASM-GR01-BND-01`: periodic/discrete boundary conventions.
- `ASM-GR01-CAL-01`: deterministic kappa calibration lock.
- `ASM-GR01-APP-02`: `ELImpliesDiscretePoissonResidual` theorem-conditional bridge status via GR01 bridge-promotion chain.

## Approximation Regime Statement

- Small perturbation parameter: `epsilon`.
- Weak-field scope: retain terms up to first order in `epsilon`.
- Neglected terms: `O(epsilon^2)` and higher.
- Domain posture: discrete 1D Poisson residual form used as theorem predicate; continuum notation is reporting shorthand only.
- 3D posture token: reporting/interpretation target is `nabla_3D^2 Phi = kappa * rho`, while theorem discharge remains at 1D residual level in v0.

## Scaling Hierarchy

- `Phi = O(epsilon)` (weak potential sector).
- `rho = O(epsilon)` in the retained source sector.
- Projected operator residual is truncated to first-order weak-field terms.
- Discrete residual representation is treated as the canonical theorem-facing object.

## Units Dictionary (Scoped)

- `Phi`: potential-like scalar (`L^2 / T^2` under standard weak-field interpretation).
- `rho`: source-density-like scalar (`M / L^3` under standard interpretation).
- `kappa`: coupling constant with calibration posture pinned by `TOE_GR01_KAPPA_CALIBRATION_v0.md`.
- Units posture is explicit for auditability and does not claim full SI discharge completeness.

## Function-Space / Regularity / Boundary Posture (v0)

- theorem-facing domain in v0 is a finite discrete lattice scalar-field surface (`ScalarField1D` / `ScalarField3D`).
- boundary posture is explicit and frozen by `ASM-GR01-BND-01` (periodic/discrete boundary conventions).
- regularity posture in v0 is discrete bounded-field regularity on finite-domain points; no continuum Sobolev-class claim is made.
- continuum operator notation is reporting shorthand layered over the discrete theorem surface.

## Integration-By-Parts And Boundary-Term Handling (explicit v0 narrative)

1. Start from first variation on the declared variational route under the default quotient path.
2. Apply the discrete summation-by-parts analogue (integration-by-parts counterpart) used by the weak-field bridge narrative.
3. Boundary-term handling is fixed by periodic/discrete boundary conventions (`ASM-GR01-BND-01`), so boundary contributions are explicitly scoped as null under that contract.
4. This v0 surface records the integration-by-parts and boundary-term contract explicitly while full derivation-grade discharge remains blocker-facing.

## Constants Normalization And Canonical Form Mapping (scoped)

- canonical weak-field reporting anchor remains `nabla^2 Phi = kappa * rho`.
- 3D reporting anchor remains `nabla_3D^2 Phi = kappa * rho`.
- calibration/normalization pointer remains `TOE_GR01_KAPPA_CALIBRATION_v0.md` (`ASM-GR01-CAL-01`).
- mapping to mainstream notation (`kappa` versus `4πG`) is scoped as a normalization layer and is not yet claimed as a fully discharged SI-identification theorem.
- canonical-equivalence theorem status: `DISCHARGED` for discrete canonical form via:
  - `formal/docs/paper/TOE_GR01_CANONICAL_EQUIVALENCE_THEOREM_v0.md`
  - claim token `TOE-GR01-EQUIV-01`.

## Analytic Derivation Chain (Narrative)

1. Start from the variational-core EL identity on the default quotient path.
2. Use `ProjectionMapWellFormed` to map core variables into weak-field potential/source representation.
3. Apply `WeakFieldTruncationSound` to isolate first-order weak-field terms under the stated scaling hierarchy.
4. Apply the bridge-promotion chain (`gr01_discrete_residual_from_bridge_promotion_chain`) to obtain a theorem-conditional emergence bridge:
   `EL = P_cubic -> DiscretePoissonResidual1D = 0`.
5. Use theorem-level transport bookkeeping (`OperatorToDiscreteResidual`) where operator-form residuals appear.
6. Read the resulting discrete residual zero statement as `PoissonEquation1D` on the theorem surface.
7. Apply calibration note `TOE_GR01_KAPPA_CALIBRATION_v0.md` only as support-layer parameter anchoring (`E-REPRO`).
8. Apply explicit 1D -> 3D mapping assumptions (`Lift1DTo3DMappingAssumptions`) to derive a conditional 3D residual statement through:
   - `discreteLaplacian3D_of_lift_x_only`,
   - `discretePoissonResidual3D_of_lift_x_only`,
   - `poissonEquation3D_of_poissonEquation1D_under_lift_x_only`.
9. Apply separable 3D mapping assumptions (`Separable3DMappingAssumptions`) to derive an improved conditional 3D residual statement through:
   - `discreteLaplacian3D_of_separable`,
   - `discretePoissonResidual3D_of_separable`,
   - `poissonEquation3D_of_componentwise_poissonEquation1D_under_separable`.
10. Apply bounded point-source assumptions (`PointSourceMappingAssumptions`) to pin a Green-class partial 3D closure posture through:
   - `gr01_mainstream3d_point_source_delta_posture_is_explicit`,
   - `gr01_mainstream3d_point_source_bounded_domain_posture`,
   - `gr01_mainstream3d_point_source_bounded_potential_behavior_posture`,
   - `gr01_mainstream3d_point_source_poissonEquation3D_under_bounded_delta_posture`,
   - `gr01_mainstream3d_point_source_partial_surface_token`.

## Assumption Minimization Audit (v0 snapshot)

| Assumption ID | Classification | Retained in v0 | Notes |
|---|---|---|---|
| `ASM-GR01-STR-01` | Mathematical necessity | YES | Transport bookkeeping from operator form to discrete residual form in current theorem route. |
| `ASM-GR01-REG-01` | Physical postulate | YES | Weak-field regime restriction defines declared scope. |
| `ASM-GR01-APP-01` | Regularity/technical constraint | YES | First-order truncation and remainder suppression contract. |
| `ASM-GR01-SYM-01` | Mathematical necessity | YES | Projection-map well-formedness for bridge composition. |
| `ASM-GR01-BND-01` | Regularity/technical constraint | YES | Periodic/discrete boundary handling contract for v0 derivation route. |
| `ASM-GR01-NRM-01` | Physical postulate | NO | Removed from theorem-facing retained set in v0; kept as reporting-only normalization note. |
| `ASM-GR01-CAL-01` | Physical postulate | YES | Deterministic calibration anchor for `kappa` posture. |
| `ASM-GR01-APP-02` | Mathematical necessity | YES | Bridge condition from EL identity to discrete Poisson residual surface. |

## Assumption Minimization Delta (v0 closure step)

- assumption-minimization status: `DISCHARGED` (v0 discrete-only).
- reduction executed:
  - `ASM-GR01-NRM-01` is removed from theorem-facing retained assumptions and reclassified to reporting-only normalization posture.
- theorem-facing retained assumption set excludes `ASM-GR01-NRM-01` in this v0 discharge package.

## Literature Alignment Mapping (v0 discrete-only CLOSED)

- literature-alignment status: `DISCHARGED` (v0 discrete-only).

| Internal derivation step | Mainstream weak-field derivation step | v0 alignment status |
|---|---|---|
| Variational action and first variation | Start from action and compute first variation | closed at theorem-surface contract level (discrete-only scope) |
| Discrete summation-by-parts (IBP analogue) | Integration by parts with boundary term handling | closed under periodic/discrete boundary contract |
| Weak-field truncation hierarchy | Weak-field approximation/truncation in perturbative regime | closed under explicit `ASM-GR01-REG-01` and `ASM-GR01-APP-01` |
| Operator-to-residual bridge (`OperatorToDiscreteResidual`) | Rearrangement into Poisson-form operator equation | closed as theorem-level bookkeeping bridge |
| `PoissonEquation1D` / `PoissonEquation3D` surfaces | Canonical Poisson equation form | closed at discrete canonical operator-form layer; continuum-limit equivalence remains out of scope in v0 |

## Current Closure Status

- Completed in v0:
  - theorem surface is non-vacuous and bridge-typed,
  - approximation regime and scaling hierarchy are explicit,
  - assumption IDs are frozen and linked,
  - assumption-minimization layer is discharged (`ASM-GR01-NRM-01` moved to reporting-only posture),
  - literature-alignment layer is discharged in discrete-only scope,
  - publication-grade derivation completeness gate status is `CLOSED` (v0 discrete-only),
  - end-to-end theorem-chain closure milestone is complete (`TOE-GR-CLS-01`).
- Remaining blockers:
  - 3D closure remains conditional on assumption-scoped transports; no full spherical/Green-function derivation-grade discharge claim is made.
  - mainstream-class 3D gate milestone remains blocker-facing:
    - `TOE-GR-3D-03`
    - `TARGET-GR01-3D-03-PLAN`
    - Track A partial theorem-surface token:
      - `gr01_mainstream3d_spherical_partial_surface_token`
      - `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DSpherical.lean`
    - Track B point-source partial theorem-surface token:
      - `gr01_mainstream3d_point_source_partial_surface_token`
      - `TARGET-GR01-3D-POINT-SOURCE-PLAN`
      - `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean`
      - `formal/docs/paper/DERIVATION_TARGET_GR01_3D_POINT_SOURCE_CLASS_v0.md`
  - action/RAC retirement items remain explicitly blocked (`BLK-01`, `BLK-02`) at state level.
  - action/RAC stance remains conditional and explicit in:
    - `formal/docs/paper/TOE_GR01_ACTION_RAC_STANCE_v0.md`

## Promotion Criteria (to remove `B-BLOCKED`)

- Maintain the tokenized end-to-end closure target (already satisfied):
  - `formal/docs/paper/DERIVATION_TARGET_GR01_END_TO_END_CLOSURE_v0.md`
  - target ID: `TARGET-GR01-END2END-CLOSURE-PLAN`
- Maintain Lean chain-composition theorem tokens:
  - `GR01EndToEndClosureBundle`
  - `gr01_end_to_end_chain_bundle_under_promoted_assumptions`
  - `gr01_end_to_end_poisson_equation_under_promoted_assumptions`
- Keep weak-field regime assumptions explicit and unchanged unless a new freeze cycle is documented.
- Complete the derivation-grade checklist target:
  - `formal/docs/paper/DERIVATION_TARGET_GR01_DERIVATION_GRADE_CHECKLIST_v0.md`
  - target ID: `TARGET-GR01-DERIV-CHECKLIST-PLAN`
- Keep improved 3D milestone token explicit:
  - `TOE-GR-3D-02`
  - `poissonEquation3D_of_componentwise_poissonEquation1D_under_separable`
- Keep mainstream-class 3D gate token explicit:
  - `TOE-GR-3D-03`
  - `formal/docs/paper/DERIVATION_TARGET_GR01_3D_MAINSTREAM_CLASS_v0.md`
- Keep Track A spherical partial theorem-surface tokens explicit:
  - `SphericalSymmetryMappingAssumptions`
  - `gr01_mainstream3d_discrete_laplacian_reduces_to_radial_under_spherical_symmetry`
  - `gr01_mainstream3d_discrete_residual_reduces_to_radial_under_spherical_symmetry`
  - `gr01_mainstream3d_poissonEquation3D_of_radial_poisson_under_spherical_symmetry`
  - `gr01_mainstream3d_spherical_partial_surface_token`
  - `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DSpherical.lean`
- Keep Track B point-source partial theorem-surface tokens explicit:
  - `TARGET-GR01-3D-POINT-SOURCE-PLAN`
  - `PointSourceMappingAssumptions`
  - `gr01_mainstream3d_point_source_delta_posture_is_explicit`
  - `gr01_mainstream3d_point_source_bounded_domain_posture`
  - `gr01_mainstream3d_point_source_bounded_potential_behavior_posture`
  - `gr01_mainstream3d_point_source_poissonEquation3D_under_bounded_delta_posture`
  - `gr01_mainstream3d_point_source_partial_surface_token`
  - `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean`
  - `formal/docs/paper/DERIVATION_TARGET_GR01_3D_POINT_SOURCE_CLASS_v0.md`
- Keep conservation compatibility theorem-surface explicit:
  - `TOE-GR-CONS-01`
  - `formal/docs/paper/TOE_GR01_CONSERVATION_COMPATIBILITY_v0.md`
- Maintain analytic/report alignment across:
  - `DERIVATION_TARGET_NEWTONIAN_LIMIT_v0.md`
  - `TOE_GR01_THEOREM_SURFACE_v0.md`
  - `TOE_GR01_PROJECTION_BRIDGE_SPEC_v0.md`
  - `ASSUMPTION_REGISTRY_v1.md`

## Promotion Maintenance Bundle (DER-02, v0)

Required to keep non-blocking conditional status:
1. Synchronize action->operator depth discharge references:
   - retain `ACTION_TO_OPERATOR_ADJUDICATION: DISCHARGED_v0_DISCRETE` in
     `DERIVATION_TARGET_GR01_ACTION_TO_OPERATOR_DISCRETE_DERIVATION_v0.md`,
   - keep bounded/discrete non-claim boundaries explicit.
2. Retain action/RAC alignment adjudication under conditional-publish endpoint:
   - `ALIGNMENT_ADJUDICATION: DISCHARGED_CONDITIONAL_PUBLISH_v0` in
     `DERIVATION_TARGET_GR01_ACTION_RAC_RETIREMENT_ALIGNMENT_v0.md`.
   - keep `BLK-01` / `BLK-02` explicit as deferred retirement blockers with
     replacement-object pointers.
3. Keep dual-format closure synchronization explicit:
   - `PILLAR-GR_PHYSICS_STATUS: CLOSED_v0_DISCRETE_CONDITIONAL`,
   - `PILLAR-GR_GOVERNANCE_STATUS: CLOSED_v0_REQUIRED_ROWS_CLEARED`,
   - `PROCEED_GATE_GR: ALLOWED_v0_PHYSICS_CLOSED`,
   - `MATRIX_CLOSURE_GATE_GR: ALLOWED_v0_GOVERNANCE_CLOSED`,
   - matrix status promotion remains a separate explicit governance action.
4. Keep derivation-grade checklist adjudication explicit:
   - `DER02_CHECKLIST_ADJUDICATION: DISCHARGED_CONDITIONAL_v0` in
     `DERIVATION_TARGET_GR01_DERIVATION_GRADE_CHECKLIST_v0.md`.
5. Preserve cross-surface lock-pointer synchronization:
   - `formal/markdown/locks/functionals/FN-DERIVE_default_quotient_hAction_provenance_v0.md`
   - `formal/markdown/locks/functionals/FN-DERIVE_default_quotient_hRAC_obligation_bundle_v0.md`
   - `formal/markdown/locks/functionals/FN-DERIVE_default_quotient_bridge_discharge_object_v0.md`
6. Preserve scope discipline:
   - no continuum/infinite-domain/uniqueness promotion,
   - no removal of explicit assumption-scoped transports.

## Falsifiability Hooks

- If first-order remainder suppression cannot be maintained in declared weak-field ranges, this derivation path is invalid.
- If 3D posture mapping (`nabla_3D^2 Phi = kappa * rho`) cannot be made explicit from pinned assumptions, 3D claims remain blocked.
- If action/RAC dependencies are removed from narrative without corresponding retirement artifacts, the closure claim is invalid.
