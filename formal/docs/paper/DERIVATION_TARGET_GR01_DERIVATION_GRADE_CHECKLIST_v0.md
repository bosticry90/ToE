# Derivation Target: GR01 Derivation-Grade Closure Checklist v0

Spec ID:
- `DERIVATION_TARGET_GR01_DERIVATION_GRADE_CHECKLIST_v0`

Target ID:
- `TARGET-GR01-DERIV-CHECKLIST-PLAN`

Classification:
- `P-POLICY`

Purpose:
- Freeze one planning-only checklist for moving `TOE-GR-01` from `B-BLOCKED` to derivation-grade closure readiness.
- Keep post-CLS scope explicit: theorem-chain composition is complete; analytic discharge package closure remains open.
- Prevent blocker drift by pinning exactly which scaffold artifacts must be upgraded.

Non-claim boundary:
- planning-only artifact.
- non-claim control surface.
- does not promote claim labels by itself.
- no comparator-lane authorization.
- no Einstein-field-equation recovery claim.
- no external truth claim.

Satisfied precondition (already closed):
- `formal/toe_formal/ToeFormal/Variational/GR01EndToEndClosure.lean`
- `gr01_end_to_end_chain_bundle_under_promoted_assumptions`
- `gr01_end_to_end_poisson_equation_under_promoted_assumptions`
- `TOE-GR-CLS-01` (`T-CONDITIONAL`)

Remaining blocker checklist (tokenized):
1. Analytic scaffold upgrades from scaffold-only to discharge-ready:
   - `formal/docs/paper/TOE_GR01_WEAK_FIELD_EXPANSION_NOTE_v0.md`
   - `formal/docs/paper/TOE_GR01_POTENTIAL_IDENTIFICATION_v0.md`
   - `formal/docs/paper/TOE_GR01_LAPLACIAN_EXTRACTION_v0.md`
   - include explicit improved 3D mapping assumptions and derived residual statement tokens:
     - `Separable3DMappingAssumptions`
     - `poissonEquation3D_of_componentwise_poissonEquation1D_under_separable`
   - keep x-only mapping tokens as embedding examples only:
     - `Lift1DTo3DMappingAssumptions`
     - `poissonEquation3D_of_poissonEquation1D_under_lift_x_only`
   - keep mainstream-class 3D gate target explicit:
     - `TARGET-GR01-3D-03-PLAN`
     - `DERIVATION_TARGET_GR01_3D_MAINSTREAM_CLASS_v0.md`
   - keep Track A spherical partial theorem-surface tokens explicit:
     - `SphericalSymmetryMappingAssumptions`
     - `gr01_mainstream3d_discrete_laplacian_reduces_to_radial_under_spherical_symmetry`
     - `gr01_mainstream3d_discrete_residual_reduces_to_radial_under_spherical_symmetry`
     - `gr01_mainstream3d_poissonEquation3D_of_radial_poisson_under_spherical_symmetry`
     - `gr01_mainstream3d_spherical_partial_surface_token`
     - `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DSpherical.lean`
   - keep Track B point-source partial theorem-surface tokens explicit:
     - `TARGET-GR01-3D-POINT-SOURCE-PLAN`
     - `PointSourceMappingAssumptions`
     - `gr01_mainstream3d_point_source_delta_posture_is_explicit`
     - `gr01_mainstream3d_point_source_bounded_domain_posture`
     - `gr01_mainstream3d_point_source_bounded_potential_behavior_posture`
     - `gr01_mainstream3d_point_source_poissonEquation3D_under_bounded_delta_posture`
     - `gr01_mainstream3d_point_source_partial_surface_token`
     - `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean`
     - `formal/docs/paper/DERIVATION_TARGET_GR01_3D_POINT_SOURCE_CLASS_v0.md`
2. Analytic discharge narrative upgrade:
   - `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md`
   - must explicitly align scaffold artifacts with the closure outputs:
     - `ProjectionMapWellFormed`
     - `WeakFieldScalingHierarchy`
     - `DiscretePoissonResidual1D` / `PoissonEquation1D`
3. Action/RAC retirement alignment remains explicit:
   - keep retirement-alignment target explicit:
     - `TARGET-GR01-ACTION-RAC-RETIREMENT-ALIGNMENT-PLAN`
     - `formal/docs/paper/DERIVATION_TARGET_GR01_ACTION_RAC_RETIREMENT_ALIGNMENT_v0.md`
   - keep upstream action-to-operator micro-target explicit:
     - `TARGET-GR01-ACTION-TO-OPERATOR-DISCRETE-DERIVATION_v0`
     - `formal/docs/paper/DERIVATION_TARGET_GR01_ACTION_TO_OPERATOR_DISCRETE_DERIVATION_v0.md`
   - keep post-closure baseline explicit while this target is open:
     - `TOE-GR-3D-03` remains `T-CONDITIONAL` under bounded/discrete v0 scope.
     - closure adjudication remains `ADJUDICATION: SATISFIED_v0_DISCRETE`.
   - keep `BLK-01` / `BLK-02` status explicit in `State_of_the_Theory.md`
   - keep action/RAC stance surface explicit:
     - `formal/docs/paper/TOE_GR01_ACTION_RAC_STANCE_v0.md`
   - closure endpoint for this pillar is fixed to:
     - `conditional-publish endpoint` (explicit non-retirement allowed, with future retirement scoped separately)
   - keep default-quotient lock pointers explicit:
     - `formal/markdown/locks/functionals/FN-DERIVE_default_quotient_hAction_provenance_v0.md`
     - `formal/markdown/locks/functionals/FN-DERIVE_default_quotient_hRAC_obligation_bundle_v0.md`
     - `formal/markdown/locks/functionals/FN-DERIVE_default_quotient_bridge_discharge_object_v0.md`
4. Cross-surface wording synchronization:
   - `formal/docs/paper/DERIVATION_TARGET_GR01_ACTION_TO_OPERATOR_DISCRETE_DERIVATION_v0.md`
   - `formal/docs/paper/DERIVATION_TARGET_NEWTONIAN_LIMIT_v0.md`
   - `formal/docs/paper/TOE_GR01_THEOREM_SURFACE_v0.md`
   - `formal/docs/paper/TOE_GR01_PROJECTION_BRIDGE_SPEC_v0.md`
   - `formal/docs/paper/RESULTS_TABLE_v0.md` (`TOE-GR-DER-02`)
   - `formal/docs/paper/STRUCTURAL_CLOSENESS_MAP_v0.md` (`TOE-GR-DER-02`)
   - `State_of_the_Theory.md`
   - improved 3D mapping milestone row token:
     - `TOE-GR-3D-02`
   - mainstream-class 3D gate milestone row token:
     - `TOE-GR-3D-03`
5. Derivation completeness gate (publication-grade tier; required before publishable promotion):
   - gate target ID:
     - `TARGET-GR01-DERIV-COMPLETENESS-GATE-PLAN`
   - gate artifact:
     - `formal/docs/paper/DERIVATION_COMPLETENESS_GATE_v0.md`
   - all gate layers must be discharged:
     - analytic discharge completeness,
     - mainstream equivalence proof to canonical weak-field form `nabla^2 Phi = kappa * rho`,
     - assumption minimization audit (mathematical necessity / physical postulate / regularity constraint),
     - literature alignment mapping (step-by-step correspondence to mainstream derivations).
   - gate fail triggers must remain explicit:
     - missing integration-by-parts step,
     - missing boundary-term handling,
     - missing function-space/regularity class,
     - missing constants normalization/units mapping,
     - missing canonical equivalence theorem.
6. Freeze constraints:
    - no new comparator lanes are authorized.
    - no new GR01 policy assumptions are added.

Status:
- theorem-chain closure milestone is complete and auditable.
- this checklist is the canonical planning surface for derivation-grade maintenance and cross-surface synchronization.
- checklist adjudication token (v0):
  - `DER02_CHECKLIST_ADJUDICATION: DISCHARGED_CONDITIONAL_v0`
