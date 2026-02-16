# Derivation Target: Newtonian Limit v0

Spec ID:
- `DERIVATION_TARGET_NEWTONIAN_LIMIT_v0`

Selected first true derivation target:
- `TOE-GR-01` (gravity weak-field sector).
- Target equation/structure: `nabla^2 Phi = kappa * rho`.
- Reporting posture token (3D): `nabla_3D^2 Phi = kappa * rho`.

Purpose:
- Upgrade the current weak-field bounded correspondence surface into a derivation-grade conditional theorem surface.
- Keep scope bounded to default quotient path and explicit assumptions.
- Freeze approximation regime and scaling hierarchy in an auditable analytic note.

Canonical assumption ledger:
- `formal/docs/paper/ASSUMPTION_REGISTRY_v1.md`

Starting point:
- Existing bounded lane/spec: `formal/quarantine/physics_target/RL03_weak_field_poisson_v0_SPEC.md`.
- Existing variational conditional bridge: `formal/toe_formal/ToeFormal/Variational/ActionRep32CubicLane.lean`.

Current scaffold artifacts (physics mode):
- theorem surface: `formal/docs/paper/TOE_GR01_THEOREM_SURFACE_v0.md`
- projection bridge spec: `formal/docs/paper/TOE_GR01_PROJECTION_BRIDGE_SPEC_v0.md`
- weak-field expansion note: `formal/docs/paper/TOE_GR01_WEAK_FIELD_EXPANSION_NOTE_v0.md`
- potential identification note: `formal/docs/paper/TOE_GR01_POTENTIAL_IDENTIFICATION_v0.md`
- Laplacian extraction note: `formal/docs/paper/TOE_GR01_LAPLACIAN_EXTRACTION_v0.md`
- analytic discharge note: `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md`
- bridge-promotion target note: `formal/docs/paper/DERIVATION_TARGET_GR01_BRIDGE_PROMOTION_v0.md`
- regime-promotion target note: `formal/docs/paper/DERIVATION_TARGET_GR01_REGIME_PROMOTION_v0.md`
- scaling-promotion target note: `formal/docs/paper/DERIVATION_TARGET_GR01_SCALING_PROMOTION_v0.md`
- symmetry-promotion target note: `formal/docs/paper/DERIVATION_TARGET_GR01_SYMMETRY_PROMOTION_v0.md`
- end-to-end closure target note: `formal/docs/paper/DERIVATION_TARGET_GR01_END_TO_END_CLOSURE_v0.md`
- kappa calibration protocol: `formal/docs/paper/TOE_GR01_KAPPA_CALIBRATION_v0.md`
- action/RAC stance policy: `formal/docs/paper/TOE_GR01_ACTION_RAC_STANCE_v0.md`
- action-to-operator depth target: `formal/docs/paper/DERIVATION_TARGET_GR01_ACTION_TO_OPERATOR_DISCRETE_DERIVATION_v0.md`
- full-derivation discharge target:
  `formal/docs/paper/DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md`
- Lean theorem module: `formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean`
- DER-01 scaffold-bundle theorem module:
  `formal/toe_formal/ToeFormal/Variational/GR01DerivationScaffoldPromotion.lean`
- default-quotient lock pointers (retirement-alignment support):
  - `formal/markdown/locks/functionals/FN-DERIVE_default_quotient_hAction_provenance_v0.md`
  - `formal/markdown/locks/functionals/FN-DERIVE_default_quotient_hRAC_obligation_bundle_v0.md`
  - `formal/markdown/locks/functionals/FN-DERIVE_default_quotient_bridge_discharge_object_v0.md`

## Derivation Checklist (Required)

1. Paper-facing theorem target
- Define a theorem surface for weak-field Poisson form under explicit assumptions.
- The theorem statement must list all assumptions (including action/RAC-side dependencies).
- v0 scaffold status: complete (theorem-shape surface added; analytic discharge pending).
- D0 status update: `PoissonEquation1D` is non-vacuous and `hPoissonLimit` input has been removed from the theorem surface.

2. Assumption promotion/classification
- Classify each assumption as theorem-level, policy-level postulate, or blocked.
- Remove hidden assumptions from the default derivation route.
- Use assumption IDs from `ASSUMPTION_REGISTRY_v1.md` in all paper/state theorem references.
- v0 bridge split status:
  - `ProjectionMapWellFormed` -> `T-CONDITIONAL` via `GR01SymmetryPromotion.lean`
  - `WeakFieldRegimePredicate` -> `T-CONDITIONAL` via `GR01BridgePromotion.lean`
  - `WeakFieldScalingHierarchy` -> `T-CONDITIONAL` via `GR01ScalingPromotion.lean`
  - `HigherOrderTermsNegligible` -> `T-CONDITIONAL` via `GR01ScalingPromotion.lean`
  - `ProjectionMapWellFormedPredicate` (auxiliary) -> `T-CONDITIONAL` via `GR01SymmetryPromotion.lean`
  - `WeakFieldTruncationSound` -> theorem-surface bridge component remains explicit;
    approximation-side discharge is carried by `gr01_first_order_truncation_sound`
  - `OperatorToDiscreteResidual` -> `T-CONDITIONAL` target
  - `ELImpliesDiscretePoissonResidual` -> `T-CONDITIONAL` via `GR01BridgePromotion.lean`
- Current dominant blocker (v5): full-derivation discharge remains open.
  Package-level governance closure is synchronized, but the default route still
  depends on action/EL bridge assumptions and placeholder/axiomatic objects
  tracked in
  `DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md`.

3. Analytic bridge note
- Provide an explicit derivation note linking the variational object to the weak-field Poisson structure in scoped regime assumptions.
- The note must include:
  - explicit approximation regime statement,
  - explicit scaling hierarchy,
  - explicit assumption freeze list with IDs.
- v0 scaffold status: complete (`TOE_GR01_ANALYTIC_DISCHARGE_v0.md` added; remaining blocker is derivation-grade analytic discharge package closure).

4. Evidence and lock surface
- Add deterministic lock artifacts and state/doc pointers for this derivation target.
- Maintain comparator evidence as support-only (`E-REPRO`) until derivation-grade closure is complete.
- v0 scaffold status: in progress (state/paper pointers and calibration lock added; projection-bridge discharge lock pending).

5. End-to-end closure criteria (tokenized; theorem-chain layer complete)
- Chain-composition theorem surface must exist and remain non-vacuous:
  - module: `formal/toe_formal/ToeFormal/Variational/GR01EndToEndClosure.lean`
  - theorem: `gr01_end_to_end_chain_bundle_under_promoted_assumptions`
- Final Poisson-form closure theorem must exist:
  - theorem: `gr01_end_to_end_poisson_equation_under_promoted_assumptions`
- Theorem chain must use promoted regime token:
  - `WeakFieldRegimePredicate`
  - `gr01_regime_predicate_under_uniform_bound`
- Composition bundle outputs must explicitly carry:
  - `ProjectionMapWellFormed`
  - `WeakFieldScalingHierarchy`
  - `DiscretePoissonResidual1D`
- 3D posture tokens must remain present (without over-claim):
  - `DiscreteLaplacian3D`
  - `DiscretePoissonResidual3D`
  - `PoissonEquation3D`
- 3D mapping assumptions + derived statement tokens must remain explicit:
  - `Separable3DMappingAssumptions`
  - `discretePoissonResidual3D_of_separable`
  - `poissonEquation3D_of_componentwise_poissonEquation1D_under_separable`
- x-only mapping tokens are retained as embedding examples, not closure-grade 3D targets:
  - `Lift1DTo3DMappingAssumptions`
  - `poissonEquation3D_of_poissonEquation1D_under_lift_x_only`
- mainstream-class 3D gate target token must remain explicit for GR closure:
  - `TARGET-GR01-3D-03-PLAN`
  - `TOE-GR-3D-03`
  - `formal/docs/paper/DERIVATION_TARGET_GR01_3D_MAINSTREAM_CLASS_v0.md`
- mainstream-class 3D closure-focused package target must remain explicit:
  - `TARGET-GR01-3D-03-CLOSURE-PACKAGE-PLAN`
  - `formal/docs/paper/DERIVATION_TARGET_GR01_3D_03_CLOSURE_PACKAGE_v0.md`
- Track A spherical partial theorem-surface tokens are pinned as first mainstream-class route:
  - `SphericalSymmetryMappingAssumptions`
  - `gr01_mainstream3d_discrete_laplacian_reduces_to_radial_under_spherical_symmetry`
  - `gr01_mainstream3d_discrete_residual_reduces_to_radial_under_spherical_symmetry`
  - `gr01_mainstream3d_poissonEquation3D_of_radial_poisson_under_spherical_symmetry`
  - `gr01_mainstream3d_spherical_partial_surface_token`
  - `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DSpherical.lean`
- Track B point-source partial theorem-surface tokens are pinned under bounded discrete posture:
  - `TARGET-GR01-3D-POINT-SOURCE-PLAN`
  - `PointSourceMappingAssumptions`
  - `gr01_mainstream3d_point_source_delta_posture_is_explicit`
  - `gr01_mainstream3d_point_source_bounded_domain_posture`
  - `gr01_mainstream3d_point_source_bounded_potential_behavior_posture`
  - `gr01_mainstream3d_point_source_poissonEquation3D_under_bounded_delta_posture`
  - `gr01_mainstream3d_point_source_partial_surface_token`
  - `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean`
  - `formal/docs/paper/DERIVATION_TARGET_GR01_3D_POINT_SOURCE_CLASS_v0.md`
- action/RAC retirement alignment target token must remain explicit:
  - `TARGET-GR01-ACTION-RAC-RETIREMENT-ALIGNMENT-PLAN`
  - `formal/docs/paper/DERIVATION_TARGET_GR01_ACTION_RAC_RETIREMENT_ALIGNMENT_v0.md`
- upstream action-to-operator depth target token must remain explicit:
  - `TARGET-GR01-ACTION-TO-OPERATOR-DISCRETE-DERIVATION_v0`
  - `formal/docs/paper/DERIVATION_TARGET_GR01_ACTION_TO_OPERATOR_DISCRETE_DERIVATION_v0.md`
- Analytic report alignment must be synchronized with:
  - `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md`
  - `formal/docs/paper/TOE_GR01_THEOREM_SURFACE_v0.md`
  - `formal/docs/paper/TOE_GR01_PROJECTION_BRIDGE_SPEC_v0.md`
- Governance anchor:
  - target ID `TARGET-GR01-END2END-CLOSURE-PLAN`
  - derivation-grade checklist target ID `TARGET-GR01-DERIV-CHECKLIST-PLAN`
  - checklist artifact: `formal/docs/paper/DERIVATION_TARGET_GR01_DERIVATION_GRADE_CHECKLIST_v0.md`

## Freeze Policy

- No new comparator lanes are authorized until `TOE-GR-01` reaches derivation-grade closure.
- Exception path requires explicit governance reset and documented approval.

## Exit Criteria

- A paper-facing theorem surface exists and is test-pinned.
- Assumption list is complete and classified.
- State doc and paper docs point to the same derivation object and lock set.
- Scope and non-claims remain explicit.
