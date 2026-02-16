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

Closure definition for this sub-target:
- theorem-surface tokens are synchronized across target/state/results.
- assumptions and bounded domain limits remain explicit.
- non-claim boundaries remain explicit.
