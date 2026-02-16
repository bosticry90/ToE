# Derivation Target: GR01 End-to-End Closure v0

Spec ID:
- `DERIVATION_TARGET_GR01_END_TO_END_CLOSURE_v0`

Target ID:
- `TARGET-GR01-END2END-CLOSURE-PLAN`

Classification:
- `P-POLICY`

Purpose:
- Freeze one planning work-order for GR01 end-to-end theorem-chain closure criteria.
- Require a single chain-composition theorem surface that stitches the promoted GR01 bridge/regime/scaling/symmetry fragments.
- Keep closure criteria tokenized and auditable across Lean + paper surfaces.

Non-claim boundary:
- planning-only artifact.
- non-claim control surface.
- does not promote claim labels by itself.
- no comparator-lane authorization.
- no Einstein-field-equation recovery claim.
- no external truth claim.

Canonical Lean pointer:
- `formal/toe_formal/ToeFormal/Variational/GR01EndToEndClosure.lean`
- `GR01EndToEndClosureBundle`
- `gr01_end_to_end_chain_bundle_under_promoted_assumptions`
- `gr01_end_to_end_poisson_equation_under_promoted_assumptions`

Assumption IDs in scope:
- `ASM-GR01-REG-01`
- `ASM-GR01-APP-01`
- `ASM-GR01-SYM-01`
- `ASM-GR01-APP-02`
- `ASM-GR01-REG-02`
- `ASM-GR01-APP-03`
- `ASM-GR01-APP-04`

Closure criteria (tokenized):
- theorem-chain composition theorem exists in Lean:
  - `gr01_end_to_end_chain_bundle_under_promoted_assumptions`
- final discrete Poisson theorem exists in Lean:
  - `gr01_end_to_end_poisson_equation_under_promoted_assumptions`
- theorem-chain uses promoted regime theorem token:
  - `WeakFieldRegimePredicate`
  - `gr01_regime_predicate_under_uniform_bound`
- theorem outputs include:
  - `ProjectionMapWellFormed`
  - `WeakFieldScalingHierarchy`
  - `DiscretePoissonResidual1D`
- analytic report alignment is explicit:
  - `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md`
  - `formal/docs/paper/TOE_GR01_THEOREM_SURFACE_v0.md`
  - `formal/docs/paper/TOE_GR01_PROJECTION_BRIDGE_SPEC_v0.md`
- no new policy assumptions are added during closure.

Status:
- weak-field assumption promotions are complete at registry level.
- theorem-chain closure criteria are satisfied under frozen scope (`TOE-GR-CLS-01`).
- remaining blocker for `TOE-GR-01` is derivation-grade analytic discharge package closure (tracked by `formal/docs/paper/DERIVATION_TARGET_GR01_DERIVATION_GRADE_CHECKLIST_v0.md`).
