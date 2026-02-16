# Derivation Target: SR Covariance Theorem Surface v0

Spec ID:
- `DERIVATION_TARGET_SR_COVARIANCE_THEOREM_SURFACE_v0`

Target ID:
- `TARGET-SR-COV-THEOREM-SURFACE-PLAN`

Parent target:
- `TARGET-SR-COV-PLAN`

Classification:
- `P-POLICY`

Purpose:
- Freeze the first SR theorem-surface scaffold under explicit assumptions.
- Define a bounded theorem-shaped contract without promoting inevitability claims.
- Synchronize theorem-surface vocabulary across target/state/results.

Adjudication token:
- `SR_COVARIANCE_THEOREM_SURFACE_ADJUDICATION_v0: DISCHARGED_v0_SCAFFOLD_CONDITIONAL_NONCLAIM`

Non-claim boundary:
- planning-only theorem-surface scaffold.
- no full SR dynamics derivation claim.
- no inevitability claim.
- no comparator-lane authorization.
- no external truth claim.

Canonical theorem-surface scaffold rows:
1. theorem token:
   - `sr_covariance_interval_invariance_surface_v0`
2. assumptions bundle token:
   - `SR_COVARIANCE_THEOREM_ASSUMPTIONS_v0`
3. domain-limit token:
   - `SR_COVARIANCE_DOMAIN_LIMITS_v0: INERTIAL_FRAMES_BOUNDED_SCOPE`
4. falsifiability token:
   - `SR_COVARIANCE_FALSIFIABILITY_HOOK_v0: EXPLICIT_INVALIDATION_CONDITION_DECLARED`

Assumption-minimization lock (cycle-014):
- baseline bundle token:
  - `SR_COVARIANCE_THEOREM_ASSUMPTIONS_v0`
- minimized bundle token:
  - `SR_COVARIANCE_THEOREM_ASSUMPTIONS_v0_min1`
- reclassification token:
  - `SR_COVARIANCE_THEOREM_RECLASSIFICATION_v0_MIN1: hInertialFrameTimeHomogeneity_POLICY_TO_MATH_via_sr_interval_invariance_surface_definition`
- ledger progress token:
  - `SR_COVARIANCE_THEOREM_ASSUMPTION_LEDGER_PROGRESS_v0: BUNDLE_MIN1_POPULATED`

Robustness/negative-control scaffold lock (cycle-015):
- robustness scaffold token:
  - `SR_COVARIANCE_THEOREM_ROBUSTNESS_SCAFFOLD_v0: TEMPLATE_PINNED`
- negative-control scaffold token:
  - `SR_COVARIANCE_THEOREM_NEGCTRL_SCAFFOLD_v0: TEMPLATE_PINNED`
- combined scaffold token:
  - `SR_COVARIANCE_THEOREM_ROBUSTNESS_NEGCTRL_SCAFFOLD_v0: CYCLE15_SCAFFOLD_LOCKED`

First robustness row lock (cycle-016):
- robustness row token:
  - `SR_COVARIANCE_THEOREM_ROBUSTNESS_ROW_01_v0: PERTURB_INTERVAL_SCALE_SMALL_PINNED`
- robustness progress token:
  - `SR_COVARIANCE_THEOREM_ROBUSTNESS_PROGRESS_v0: ROW_01_POPULATED`

First negative-control row lock (cycle-017):
- negative-control row token:
  - `SR_COVARIANCE_THEOREM_NEGCTRL_ROW_01_v0: BROKEN_INTERVAL_INVARIANCE_ASSUMPTION_PINNED`
- negative-control progress token:
  - `SR_COVARIANCE_THEOREM_NEGCTRL_PROGRESS_v0: ROW_01_POPULATED`

Second robustness row lock (cycle-018):
- robustness row token:
  - `SR_COVARIANCE_THEOREM_ROBUSTNESS_ROW_02_v0: PERTURB_VELOCITY_COMPOSITION_SMALL_PINNED`
- robustness progress token:
  - `SR_COVARIANCE_THEOREM_ROBUSTNESS_PROGRESS_v0: ROW_02_POPULATED`

Second negative-control row lock (cycle-019):
- negative-control row token:
  - `SR_COVARIANCE_THEOREM_NEGCTRL_ROW_02_v0: BROKEN_VELOCITY_COMPOSITION_CLOSURE_ASSUMPTION_PINNED`
- negative-control progress token:
  - `SR_COVARIANCE_THEOREM_NEGCTRL_PROGRESS_v0: ROW_02_POPULATED`

Robustness/negative-control family completion lock (cycle-020):
- robustness completion token:
  - `SR_COVARIANCE_THEOREM_ROBUSTNESS_PROGRESS_v0: ALL_REQUIRED_ROWS_POPULATED`
- negative-control completion token:
  - `SR_COVARIANCE_THEOREM_NEGCTRL_PROGRESS_v0: ALL_REQUIRED_ROWS_POPULATED`
- family completion token:
  - `SR_COVARIANCE_THEOREM_ROBUSTNESS_NEGCTRL_FAMILY_COMPLETION_v0: CYCLE20_LOCKED`

Pre-discharge criteria lock (cycle-021):
- criteria token:
  - `SR_COVARIANCE_THEOREM_PREDISCHARGE_CRITERIA_v0: CYCLE21_ROW_LEVEL_CRITERIA_PINNED`
- criteria rows:
  - `SR_COVARIANCE_THEOREM_CRITERIA_ROW_01_v0: ASSUMPTION_MINIMIZATION_LOCKED`
  - `SR_COVARIANCE_THEOREM_CRITERIA_ROW_02_v0: ROBUSTNESS_ROWS_LOCKED`
  - `SR_COVARIANCE_THEOREM_CRITERIA_ROW_03_v0: NEGCTRL_ROWS_LOCKED`
  - `SR_COVARIANCE_THEOREM_CRITERIA_ROW_04_v0: RESULTS_SYNC_LOCKED`

Cycle-013 synchronization lock:
- micro-target token:
  - `TARGET-SR-COV-MICRO-13-THEOREM-SURFACE-SCAFFOLD-v0`
- progress token:
  - `SR_COVARIANCE_PROGRESS_CYCLE13_v0: THEOREM_SURFACE_SCAFFOLD_TOKEN_PINNED`
- artifact token:
  - `SR_COVARIANCE_CYCLE13_ARTIFACT_v0: sr_covariance_theorem_surface_scaffold_cycle13_v0`
- artifact pointer:
  - `formal/output/sr_covariance_theorem_surface_scaffold_cycle13_v0.json`

Cycle-014 synchronization lock:
- micro-target token:
  - `TARGET-SR-COV-MICRO-14-THEOREM-ASSUMPTION-MINIMIZATION-v0`
- minimization token:
  - `SR_COVARIANCE_THEOREM_ASSUMPTION_MINIMIZATION_v0: CYCLE14_MIN1_LOCKED`
- progress token:
  - `SR_COVARIANCE_PROGRESS_CYCLE14_v0: THEOREM_ASSUMPTION_MINIMIZATION_TOKEN_PINNED`
- artifact token:
  - `SR_COVARIANCE_CYCLE14_ARTIFACT_v0: sr_covariance_theorem_assumption_minimization_cycle14_v0`
- artifact pointer:
  - `formal/output/sr_covariance_theorem_assumption_minimization_cycle14_v0.json`

Cycle-015 synchronization lock:
- micro-target token:
  - `TARGET-SR-COV-MICRO-15-THEOREM-ROBUSTNESS-NEGCTRL-SCAFFOLD-v0`
- scaffold lock token:
  - `SR_COVARIANCE_THEOREM_ROBUSTNESS_NEGCTRL_SCAFFOLD_v0: CYCLE15_SCAFFOLD_LOCKED`
- progress token:
  - `SR_COVARIANCE_PROGRESS_CYCLE15_v0: THEOREM_ROBUSTNESS_NEGCTRL_SCAFFOLD_TOKEN_PINNED`
- artifact token:
  - `SR_COVARIANCE_CYCLE15_ARTIFACT_v0: sr_covariance_theorem_robustness_negctrl_scaffold_cycle15_v0`
- artifact pointer:
  - `formal/output/sr_covariance_theorem_robustness_negctrl_scaffold_cycle15_v0.json`

Cycle-016 synchronization lock:
- micro-target token:
  - `TARGET-SR-COV-MICRO-16-THEOREM-ROBUSTNESS-ROW1-v0`
- robustness row token:
  - `SR_COVARIANCE_THEOREM_ROBUSTNESS_ROW_01_v0: PERTURB_INTERVAL_SCALE_SMALL_PINNED`
- cycle token:
  - `SR_COVARIANCE_PROGRESS_CYCLE16_v0: THEOREM_ROBUSTNESS_ROW1_TOKEN_PINNED`
- artifact token:
  - `SR_COVARIANCE_CYCLE16_ARTIFACT_v0: sr_covariance_theorem_robustness_row1_cycle16_v0`
- artifact pointer:
  - `formal/output/sr_covariance_theorem_robustness_row1_cycle16_v0.json`

Cycle-017 synchronization lock:
- micro-target token:
  - `TARGET-SR-COV-MICRO-17-THEOREM-NEGCTRL-ROW1-v0`
- negative-control row token:
  - `SR_COVARIANCE_THEOREM_NEGCTRL_ROW_01_v0: BROKEN_INTERVAL_INVARIANCE_ASSUMPTION_PINNED`
- cycle token:
  - `SR_COVARIANCE_PROGRESS_CYCLE17_v0: THEOREM_NEGCTRL_ROW1_TOKEN_PINNED`
- artifact token:
  - `SR_COVARIANCE_CYCLE17_ARTIFACT_v0: sr_covariance_theorem_negctrl_row1_cycle17_v0`
- artifact pointer:
  - `formal/output/sr_covariance_theorem_negctrl_row1_cycle17_v0.json`

Cycle-018 synchronization lock:
- micro-target token:
  - `TARGET-SR-COV-MICRO-18-THEOREM-ROBUSTNESS-ROW2-v0`
- robustness row token:
  - `SR_COVARIANCE_THEOREM_ROBUSTNESS_ROW_02_v0: PERTURB_VELOCITY_COMPOSITION_SMALL_PINNED`
- cycle token:
  - `SR_COVARIANCE_PROGRESS_CYCLE18_v0: THEOREM_ROBUSTNESS_ROW2_TOKEN_PINNED`
- artifact token:
  - `SR_COVARIANCE_CYCLE18_ARTIFACT_v0: sr_covariance_theorem_robustness_row2_cycle18_v0`
- artifact pointer:
  - `formal/output/sr_covariance_theorem_robustness_row2_cycle18_v0.json`

Cycle-019 synchronization lock:
- micro-target token:
  - `TARGET-SR-COV-MICRO-19-THEOREM-NEGCTRL-ROW2-v0`
- negative-control row token:
  - `SR_COVARIANCE_THEOREM_NEGCTRL_ROW_02_v0: BROKEN_VELOCITY_COMPOSITION_CLOSURE_ASSUMPTION_PINNED`
- cycle token:
  - `SR_COVARIANCE_PROGRESS_CYCLE19_v0: THEOREM_NEGCTRL_ROW2_TOKEN_PINNED`
- artifact token:
  - `SR_COVARIANCE_CYCLE19_ARTIFACT_v0: sr_covariance_theorem_negctrl_row2_cycle19_v0`
- artifact pointer:
  - `formal/output/sr_covariance_theorem_negctrl_row2_cycle19_v0.json`

Cycle-020 synchronization lock:
- micro-target token:
  - `TARGET-SR-COV-MICRO-20-THEOREM-ROBUSTNESS-NEGCTRL-FAMILY-COMPLETE-v0`
- family completion token:
  - `SR_COVARIANCE_THEOREM_ROBUSTNESS_NEGCTRL_FAMILY_COMPLETION_v0: CYCLE20_LOCKED`
- cycle token:
  - `SR_COVARIANCE_PROGRESS_CYCLE20_v0: THEOREM_ROBUSTNESS_NEGCTRL_FAMILY_COMPLETION_TOKEN_PINNED`
- artifact token:
  - `SR_COVARIANCE_CYCLE20_ARTIFACT_v0: sr_covariance_theorem_robustness_negctrl_family_completion_cycle20_v0`
- artifact pointer:
  - `formal/output/sr_covariance_theorem_robustness_negctrl_family_completion_cycle20_v0.json`

Cycle-021 synchronization lock:
- micro-target token:
  - `TARGET-SR-COV-MICRO-21-THEOREM-PREDISCHARGE-CRITERIA-v0`
- criteria token:
  - `SR_COVARIANCE_THEOREM_PREDISCHARGE_CRITERIA_v0: CYCLE21_ROW_LEVEL_CRITERIA_PINNED`
- cycle token:
  - `SR_COVARIANCE_PROGRESS_CYCLE21_v0: THEOREM_PREDISCHARGE_CRITERIA_TOKEN_PINNED`
- artifact token:
  - `SR_COVARIANCE_CYCLE21_ARTIFACT_v0: sr_covariance_theorem_predischarge_criteria_cycle21_v0`
- artifact pointer:
  - `formal/output/sr_covariance_theorem_predischarge_criteria_cycle21_v0.json`

Cycle-022 synchronization lock:
- micro-target token:
  - `TARGET-SR-COV-MICRO-22-THEOREM-ADJUDICATION-TRANSITION-v0`
- adjudication token:
  - `SR_COVARIANCE_THEOREM_SURFACE_ADJUDICATION_v0: DISCHARGED_v0_PREDISCHARGE_CRITERIA_LOCKED_NONCLAIM`
- cycle token:
  - `SR_COVARIANCE_PROGRESS_CYCLE22_v0: THEOREM_ADJUDICATION_TRANSITION_TOKEN_PINNED`
- artifact token:
  - `SR_COVARIANCE_CYCLE22_ARTIFACT_v0: sr_covariance_theorem_adjudication_transition_cycle22_v0`
- artifact pointer:
  - `formal/output/sr_covariance_theorem_adjudication_transition_cycle22_v0.json`

Cycle-023 synchronization lock:
- micro-target token:
  - `TARGET-SR-COV-MICRO-23-THEOREM-PACKAGE-FREEZE-v0`
- package-freeze token:
  - `SR_COVARIANCE_THEOREM_PACKAGE_FREEZE_v0: CYCLE23_FROZEN_CONTENTS_PINNED`
- cycle token:
  - `SR_COVARIANCE_PROGRESS_CYCLE23_v0: THEOREM_PACKAGE_FREEZE_TOKEN_PINNED`
- artifact token:
  - `SR_COVARIANCE_CYCLE23_ARTIFACT_v0: sr_covariance_theorem_package_freeze_cycle23_v0`
- artifact pointer:
  - `formal/output/sr_covariance_theorem_package_freeze_cycle23_v0.json`

Cycle-024 synchronization lock:
- micro-target token:
  - `TARGET-SR-COV-MICRO-24-THEOREM-FROZEN-WATCH-REOPEN-POLICY-v0`
- reopen-policy token:
  - `SR_COVARIANCE_THEOREM_REOPEN_POLICY_v0: FROZEN_WATCH_REOPEN_ON_REGRESSION`
- cycle token:
  - `SR_COVARIANCE_PROGRESS_CYCLE24_v0: THEOREM_FROZEN_WATCH_REOPEN_POLICY_TOKEN_PINNED`
- artifact token:
  - `SR_COVARIANCE_CYCLE24_ARTIFACT_v0: sr_covariance_theorem_frozen_watch_reopen_policy_cycle24_v0`
- artifact pointer:
  - `formal/output/sr_covariance_theorem_frozen_watch_reopen_policy_cycle24_v0.json`

Cycle-025 synchronization lock:
- micro-target token:
  - `TARGET-SR-COV-MICRO-25-THEOREM-DERIVATION-PROMOTION-GATE-v0`
- derivation-promotion gate token:
  - `SR_COVARIANCE_THEOREM_DERIVATION_PROMOTION_GATE_v0: CYCLE25_CRITERIA_LOCKED_NONCLAIM`
- cycle token:
  - `SR_COVARIANCE_PROGRESS_CYCLE25_v0: THEOREM_DERIVATION_PROMOTION_GATE_TOKEN_PINNED`
- artifact token:
  - `SR_COVARIANCE_CYCLE25_ARTIFACT_v0: sr_covariance_theorem_derivation_promotion_gate_cycle25_v0`
- artifact pointer:
  - `formal/output/sr_covariance_theorem_derivation_promotion_gate_cycle25_v0.json`

Cycle-026 synchronization lock:
- micro-target token:
  - `TARGET-SR-COV-MICRO-26-DERIVATION-COMPLETENESS-GATE-SCAFFOLD-v0`
- derivation-completeness target token:
  - `TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN`
- derivation-completeness target pointer:
  - `formal/docs/paper/DERIVATION_TARGET_SR_DERIVATION_COMPLETENESS_GATE_v0.md`
- derivation-completeness gate token:
  - `SR_DERIVATION_COMPLETENESS_GATE_v0: CYCLE26_SCAFFOLD_PINNED_NONCLAIM`
- cycle token:
  - `SR_COVARIANCE_PROGRESS_CYCLE26_v0: DERIVATION_COMPLETENESS_GATE_SCAFFOLD_TOKEN_PINNED`
- artifact token:
  - `SR_COVARIANCE_CYCLE26_ARTIFACT_v0: sr_covariance_derivation_completeness_gate_scaffold_cycle26_v0`
- artifact pointer:
  - `formal/output/sr_covariance_derivation_completeness_gate_scaffold_cycle26_v0.json`

Cycle-027 synchronization lock:
- micro-target token:
  - `TARGET-SR-COV-MICRO-27-THEOREM-OBJECT-IMPLEMENTATION-GATE-v0`
- theorem-object implementation gate token:
  - `SR_COVARIANCE_THEOREM_OBJECT_IMPLEMENTATION_GATE_v0: CYCLE27_BASE_OBJECT_SET_PINNED_NONCLAIM`
- cycle token:
  - `SR_COVARIANCE_PROGRESS_CYCLE27_v0: THEOREM_OBJECT_IMPLEMENTATION_GATE_TOKEN_PINNED`
- artifact token:
  - `SR_COVARIANCE_CYCLE27_ARTIFACT_v0: sr_covariance_theorem_object_implementation_gate_cycle27_v0`
- artifact pointer:
  - `formal/output/sr_covariance_theorem_object_implementation_gate_cycle27_v0.json`

Cycle-028 synchronization lock:
- micro-target token:
  - `TARGET-SR-COV-MICRO-28-THEOREM-OBJECT-DISCHARGE-STUB-v0`
- theorem-object discharge stub token:
  - `SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_STUB_v0: CYCLE28_BASE_THEOREM_SIGNATURES_PINNED_NONCLAIM`
- lean module pointer:
  - `formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean`
- cycle token:
  - `SR_COVARIANCE_PROGRESS_CYCLE28_v0: THEOREM_OBJECT_DISCHARGE_STUB_TOKEN_PINNED`
- artifact token:
  - `SR_COVARIANCE_CYCLE28_ARTIFACT_v0: sr_covariance_theorem_object_discharge_stub_cycle28_v0`
- artifact pointer:
  - `formal/output/sr_covariance_theorem_object_discharge_stub_cycle28_v0.json`

Cycle-029 synchronization lock:
- micro-target token:
  - `TARGET-SR-COV-MICRO-29-THEOREM-OBJECT-PHASE-EXIT-BINDING-v0`
- theorem-object phase-exit binding token:
  - `SR_COVARIANCE_THEOREM_OBJECT_PHASE_EXIT_BINDING_v0: CYCLE29_PHASE_EXIT_TOKENS_PINNED_NONCLAIM`
- canonical phase-exit token map:
  - `SR_FULL_DERIVATION_PHASE1_EXIT_v0: OBJECT_THEOREM_SURFACES_BOUND_NONCLAIM`
  - `SR_FULL_DERIVATION_PHASE2_EXIT_v0: CANONICAL_EQUIVALENCE_SURFACE_BOUND_NONCLAIM`
  - `SR_FULL_DERIVATION_PHASE3_EXIT_v0: ASSUMPTION_MINIMIZATION_DISCHARGE_BOUND_NONCLAIM`
  - `SR_FULL_DERIVATION_PHASE4_EXIT_v0: ROBUSTNESS_NEGCTRL_DISCHARGE_BOUND_NONCLAIM`
  - `SR_FULL_DERIVATION_PHASE5_EXIT_v0: DERIVATION_COMPLETENESS_GATE_DISCHARGE_BOUND_NONCLAIM`
  - `SR_FULL_DERIVATION_PHASE6_EXIT_v0: INEVITABILITY_GATE_DISCHARGE_BOUND_NONCLAIM`
  - `SR_FULL_DERIVATION_PHASE7_EXIT_v0: PACKAGE_FREEZE_REOPEN_POLICY_BOUND_NONCLAIM`
- roadmap pointer:
  - `formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md`
- cycle token:
  - `SR_COVARIANCE_PROGRESS_CYCLE29_v0: THEOREM_OBJECT_PHASE_EXIT_BINDING_TOKEN_PINNED`
- artifact token:
  - `SR_COVARIANCE_CYCLE29_ARTIFACT_v0: sr_covariance_theorem_object_phase_exit_binding_cycle29_v0`
- artifact pointer:
  - `formal/output/sr_covariance_theorem_object_phase_exit_binding_cycle29_v0.json`

Cycle-030 synchronization lock:
- micro-target token:
  - `TARGET-SR-COV-MICRO-30-THEOREM-OBJECT-DISCHARGE-PROGRESSION-v0`
- theorem-object discharge progression token:
  - `SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_PROGRESSION_v0: CYCLE30_PHASE1_DISCHARGE_PROGRESS_PINNED_NONCLAIM`
- phase-I discharge row tokens:
  - `SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_01_v0: LORENTZ_TRANSFORM_OBJECT_SURFACE_PROGRESS_PINNED`
  - `SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_02_v0: INTERVAL_INVARIANCE_SURFACE_PROGRESS_PINNED`
  - `SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_03_v0: VELOCITY_COMPOSITION_SURFACE_PROGRESS_PINNED`
  - `SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_04_v0: COVARIANCE_CONTRACT_SURFACE_PROGRESS_PINNED`
- phase-I discharge progress token:
  - `SR_FULL_DERIVATION_PHASE1_DISCHARGE_PROGRESS_v0: ROWS_01_04_POPULATED_NONCLAIM`
- roadmap pointer:
  - `formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md`
- cycle token:
  - `SR_COVARIANCE_PROGRESS_CYCLE30_v0: THEOREM_OBJECT_DISCHARGE_PROGRESSION_TOKEN_PINNED`
- artifact token:
  - `SR_COVARIANCE_CYCLE30_ARTIFACT_v0: sr_covariance_theorem_object_discharge_progression_cycle30_v0`
- artifact pointer:
  - `formal/output/sr_covariance_theorem_object_discharge_progression_cycle30_v0.json`

Cycle-031 synchronization lock:
- micro-target token:
  - `TARGET-SR-COV-MICRO-31-THEOREM-OBJECT-DISCHARGE-ROW01-LOCK-v0`
- theorem-object discharge row-01 lock token:
  - `SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_ROW01_LOCK_v0: CYCLE31_PHASE1_ROW01_DISCHARGE_PINNED_NONCLAIM`
- phase-I row-01 discharge status token:
  - `SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_01_STATUS_v0: LORENTZ_TRANSFORM_OBJECT_SURFACE_DISCHARGE_PINNED_NONCLAIM`
- phase-I row-lock progress token:
  - `SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_DISCHARGE_PINNED_NONCLAIM`
- roadmap pointer:
  - `formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md`
- cycle token:
  - `SR_COVARIANCE_PROGRESS_CYCLE31_v0: THEOREM_OBJECT_DISCHARGE_ROW01_LOCK_TOKEN_PINNED`
- artifact token:
  - `SR_COVARIANCE_CYCLE31_ARTIFACT_v0: sr_covariance_theorem_object_discharge_row01_lock_cycle31_v0`
- artifact pointer:
  - `formal/output/sr_covariance_theorem_object_discharge_row01_lock_cycle31_v0.json`

Cycle-032 synchronization lock:
- micro-target token:
  - `TARGET-SR-COV-MICRO-32-THEOREM-OBJECT-DISCHARGE-ROW02-LOCK-v0`
- theorem-object discharge row-02 lock token:
  - `SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_ROW02_LOCK_v0: CYCLE32_PHASE1_ROW02_DISCHARGE_PINNED_NONCLAIM`
- phase-I row-02 discharge status token:
  - `SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_02_STATUS_v0: INTERVAL_INVARIANCE_SURFACE_DISCHARGE_PINNED_NONCLAIM`
- phase-I row-lock progress token:
  - `SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_DISCHARGE_PINNED_NONCLAIM`
- roadmap pointer:
  - `formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md`
- cycle token:
  - `SR_COVARIANCE_PROGRESS_CYCLE32_v0: THEOREM_OBJECT_DISCHARGE_ROW02_LOCK_TOKEN_PINNED`
- artifact token:
  - `SR_COVARIANCE_CYCLE32_ARTIFACT_v0: sr_covariance_theorem_object_discharge_row02_lock_cycle32_v0`
- artifact pointer:
  - `formal/output/sr_covariance_theorem_object_discharge_row02_lock_cycle32_v0.json`

Cycle-033 synchronization lock:
- micro-target token:
  - `TARGET-SR-COV-MICRO-33-THEOREM-OBJECT-DISCHARGE-ROW03-LOCK-v0`
- theorem-object discharge row-03 lock token:
  - `SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_ROW03_LOCK_v0: CYCLE33_PHASE1_ROW03_DISCHARGE_PINNED_NONCLAIM`
- phase-I row-03 discharge status token:
  - `SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_03_STATUS_v0: VELOCITY_COMPOSITION_SURFACE_DISCHARGE_PINNED_NONCLAIM`
- phase-I row-lock progress token:
  - `SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_DISCHARGE_PINNED_NONCLAIM`
- roadmap pointer:
  - `formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md`
- cycle token:
  - `SR_COVARIANCE_PROGRESS_CYCLE33_v0: THEOREM_OBJECT_DISCHARGE_ROW03_LOCK_TOKEN_PINNED`
- artifact token:
  - `SR_COVARIANCE_CYCLE33_ARTIFACT_v0: sr_covariance_theorem_object_discharge_row03_lock_cycle33_v0`
- artifact pointer:
  - `formal/output/sr_covariance_theorem_object_discharge_row03_lock_cycle33_v0.json`

Cycle-034 synchronization lock:
- micro-target token:
  - `TARGET-SR-COV-MICRO-34-THEOREM-OBJECT-DISCHARGE-ROW04-LOCK-v0`
- theorem-object discharge row-04 lock token:
  - `SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_ROW04_LOCK_v0: CYCLE34_PHASE1_ROW04_DISCHARGE_PINNED_NONCLAIM`
- phase-I row-04 discharge status token:
  - `SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_04_STATUS_v0: COVARIANCE_CONTRACT_SURFACE_DISCHARGE_PINNED_NONCLAIM`
- phase-I row-lock progress token:
  - `SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_ROW04_DISCHARGE_PINNED_NONCLAIM`
- roadmap pointer:
  - `formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md`
- cycle token:
  - `SR_COVARIANCE_PROGRESS_CYCLE34_v0: THEOREM_OBJECT_DISCHARGE_ROW04_LOCK_TOKEN_PINNED`
- artifact token:
  - `SR_COVARIANCE_CYCLE34_ARTIFACT_v0: sr_covariance_theorem_object_discharge_row04_lock_cycle34_v0`
- artifact pointer:
  - `formal/output/sr_covariance_theorem_object_discharge_row04_lock_cycle34_v0.json`

Closure definition for this sub-target:
- theorem-surface tokens are synchronized across target/state/results.
- assumptions and bounded domain limits remain explicit.
- non-claim boundaries remain explicit.
