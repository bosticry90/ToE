# Derivation Target: SR Covariance Object v0

Spec ID:
- `DERIVATION_TARGET_SR_COVARIANCE_OBJECT_v0`

Target ID:
- `TARGET-SR-COV-PLAN`

Classification:
- `P-POLICY`

Purpose:
- Freeze one planning-only SR target for covariance/kinematics closure posture.
- Keep Lorentz posture explicit under bounded assumptions.
- Define the first nontrivial SR object set to unlock immediately after GR01 derivation-grade closure.

Non-claim boundary:
- planning-only artifact.
- non-claim control surface.
- does not promote claim labels by itself.
- no comparator-lane authorization.
- no full relativistic field-theory completion claim.
- no external truth claim.

Minimum structural objects required:
- spacetime transform object
- invariant interval or equivalent invariant structure
- velocity-composition/kinematics object
- explicit covariance contract

Canonical SR object checklist (v0 planning):
1. Lorentz transform object:
   - typed map between inertial coordinate frames.
2. Invariant interval object:
   - explicit scalar invariant preserved by transform object.
3. Covariance contract:
   - theorem-shaped contract for transform invariance under declared assumptions.
4. Domain limits:
   - explicit assumptions for weak-field/non-accelerating frame usage if bounded.
5. Falsifiability hook:
   - explicit statement of what would invalidate covariance posture in this scoped target.

Unlock condition:
- `LOCKED` until `TARGET-GR01-DERIV-CHECKLIST-PLAN` is `CLOSED` in `PHYSICS_ROADMAP_v0.md`.

Closure definition:
- typed SR theorem/derivation surface exists with explicit assumptions.
- explicit statement of covariance posture and domain limits.
- paper/state/results pointers are synchronized.

Cycle-001 kickoff micro-targets (now pinned):
1. `TARGET-SR-COV-MICRO-01-OBJECT-SCAFFOLD-v0`
    - scope:
       - planning-only typed-object scaffold for SR covariance lane entry.
    - cycle token:
       - `SR_COVARIANCE_PROGRESS_v0: CYCLE1_OBJECT_SCAFFOLD_TOKEN_PINNED`
    - artifact token:
       - `SR_COVARIANCE_CYCLE1_ARTIFACT_v0: sr_covariance_object_scaffold_cycle1_v0`
    - artifact pointer:
       - `formal/output/sr_covariance_object_scaffold_cycle1_v0.json`
    - gate posture:
       - non-claim wording remains explicit and no claim promotion is authorized.

Cycle-002 kickoff micro-targets (now pinned):
1. `TARGET-SR-COV-MICRO-02-CONTRACT-SURFACE-v0`
    - scope:
       - planning-only covariance contract-surface specification scaffold.
    - cycle token:
       - `SR_COVARIANCE_PROGRESS_CYCLE2_v0: CONTRACT_SURFACE_TOKEN_PINNED`
    - artifact token:
       - `SR_COVARIANCE_CYCLE2_ARTIFACT_v0: sr_covariance_contract_surface_cycle2_v0`
    - artifact pointer:
       - `formal/output/sr_covariance_contract_surface_cycle2_v0.json`
    - gate posture:
       - non-claim wording remains explicit and no theorem/evidence promotion is authorized.

Cycle-003 kickoff micro-targets (now pinned):
1. `TARGET-SR-COV-MICRO-03-LORENTZ-INTERVAL-PLACEHOLDER-v0`
    - scope:
       - planning-only placeholder for typed Lorentz + invariant-interval contract surface.
    - cycle token:
       - `SR_COVARIANCE_PROGRESS_CYCLE3_v0: LORENTZ_INTERVAL_PLACEHOLDER_TOKEN_PINNED`
    - artifact token:
       - `SR_COVARIANCE_CYCLE3_ARTIFACT_v0: sr_covariance_lorentz_interval_placeholder_cycle3_v0`
    - artifact pointer:
       - `formal/output/sr_covariance_lorentz_interval_placeholder_cycle3_v0.json`
    - gate posture:
       - remains planning-only/non-claim and does not promote theorem/evidence status.

Cycle-004 kickoff micro-targets (now pinned):
1. `TARGET-SR-COV-MICRO-04-VELOCITY-COMPOSITION-PLACEHOLDER-v0`
    - scope:
       - planning-only placeholder for typed velocity-composition/kinematics contract surface.
    - cycle token:
       - `SR_COVARIANCE_PROGRESS_CYCLE4_v0: VELOCITY_COMPOSITION_PLACEHOLDER_TOKEN_PINNED`
    - artifact token:
       - `SR_COVARIANCE_CYCLE4_ARTIFACT_v0: sr_covariance_velocity_composition_placeholder_cycle4_v0`
    - artifact pointer:
       - `formal/output/sr_covariance_velocity_composition_placeholder_cycle4_v0.json`
    - gate posture:
       - remains planning-only/non-claim and does not promote theorem/evidence status.

Cycle-005 kickoff micro-targets (now pinned):
1. `TARGET-SR-COV-MICRO-05-INTEGRATED-KICKOFF-BUNDLE-v0`
    - scope:
       - planning-only integrated bundle lock across cycle-001 .. cycle-005 kickoff surfaces.
    - cycle token:
       - `SR_COVARIANCE_PROGRESS_CYCLE5_v0: INTEGRATED_KICKOFF_BUNDLE_TOKEN_PINNED`
    - artifact token:
       - `SR_COVARIANCE_CYCLE5_ARTIFACT_v0: sr_covariance_integrated_kickoff_bundle_cycle5_v0`
    - artifact pointer:
       - `formal/output/sr_covariance_integrated_kickoff_bundle_cycle5_v0.json`
    - gate posture:
       - remains planning-only/non-claim and does not promote theorem/evidence status.

Cycle-006 kickoff micro-targets (now pinned):
1. `TARGET-SR-COV-MICRO-06-PREDISCHARGE-GATE-BUNDLE-v0`
    - scope:
       - planning-only pre-discharge gate-bundle lock for SR covariance kickoff stack.
    - cycle token:
       - `SR_COVARIANCE_PROGRESS_CYCLE6_v0: PREDISCHARGE_GATE_BUNDLE_TOKEN_PINNED`
    - artifact token:
       - `SR_COVARIANCE_CYCLE6_ARTIFACT_v0: sr_covariance_predischarge_gate_bundle_cycle6_v0`
    - artifact pointer:
       - `formal/output/sr_covariance_predischarge_gate_bundle_cycle6_v0.json`
    - gate posture:
       - remains planning-only/non-claim and does not promote theorem/evidence status.

Cycle-007 kickoff micro-targets (now pinned):
1. `TARGET-SR-COV-MICRO-07-DISCHARGE-TRANSITION-BUNDLE-v0`
    - scope:
       - planning-only discharge-transition bundle lock for SR covariance kickoff stack.
    - cycle token:
       - `SR_COVARIANCE_PROGRESS_CYCLE7_v0: DISCHARGE_TRANSITION_BUNDLE_TOKEN_PINNED`
    - artifact token:
       - `SR_COVARIANCE_CYCLE7_ARTIFACT_v0: sr_covariance_discharge_transition_bundle_cycle7_v0`
    - artifact pointer:
       - `formal/output/sr_covariance_discharge_transition_bundle_cycle7_v0.json`
    - gate posture:
       - remains planning-only/non-claim and does not promote theorem/evidence status.

Cycle-008 kickoff micro-targets (now pinned):
1. `TARGET-SR-COV-MICRO-08-KEYB-POLICY-SIGNOFF-BUNDLE-v0`
    - scope:
       - planning-only key-B policy signoff bundle lock for SR covariance kickoff stack.
    - cycle token:
       - `SR_COVARIANCE_PROGRESS_CYCLE8_v0: KEYB_POLICY_SIGNOFF_BUNDLE_TOKEN_PINNED`
    - artifact token:
       - `SR_COVARIANCE_CYCLE8_ARTIFACT_v0: sr_covariance_keyb_policy_signoff_bundle_cycle8_v0`
    - artifact pointer:
       - `formal/output/sr_covariance_keyb_policy_signoff_bundle_cycle8_v0.json`
    - gate posture:
       - remains planning-only/non-claim and does not promote theorem/evidence status.

Cycle-009 kickoff micro-targets (now pinned):
1. `TARGET-SR-COV-MICRO-09-FINAL-PREDISCHARGE-PACKAGE-v0`
    - scope:
       - planning-only final pre-discharge package lock for SR covariance kickoff stack.
    - cycle token:
       - `SR_COVARIANCE_PROGRESS_CYCLE9_v0: FINAL_PREDISCHARGE_PACKAGE_TOKEN_PINNED`
    - artifact token:
       - `SR_COVARIANCE_CYCLE9_ARTIFACT_v0: sr_covariance_final_predischarge_package_cycle9_v0`
    - artifact pointer:
       - `formal/output/sr_covariance_final_predischarge_package_cycle9_v0.json`
    - gate posture:
       - remains planning-only/non-claim and does not promote theorem/evidence status.

Cycle-010 integrated discharge-criteria lock (now pinned):
- `SR_COVARIANCE_DISCHARGE_CRITERIA_v0: CYCLE10_ROW_LEVEL_CRITERIA_PINNED`
- criteria rows:
   - `SR_COVARIANCE_CRITERIA_ROW_01_v0: OBJECT_SCAFFOLD_PINNED`
   - `SR_COVARIANCE_CRITERIA_ROW_02_v0: CONTRACT_SURFACE_PINNED`
   - `SR_COVARIANCE_CRITERIA_ROW_03_v0: LORENTZ_INTERVAL_PLACEHOLDER_PINNED`
   - `SR_COVARIANCE_CRITERIA_ROW_04_v0: VELOCITY_COMPOSITION_PLACEHOLDER_PINNED`
   - `SR_COVARIANCE_CRITERIA_ROW_05_v0: STATE_GATE_SYNC_PINNED`
- cycle token:
   - `SR_COVARIANCE_PROGRESS_CYCLE10_v0: DISCHARGE_CRITERIA_LOCK_TOKEN_PINNED`
- artifact token:
   - `SR_COVARIANCE_CYCLE10_ARTIFACT_v0: sr_covariance_discharge_criteria_cycle10_v0`
- artifact pointer:
   - `formal/output/sr_covariance_discharge_criteria_cycle10_v0.json`
- gate posture:
   - remains planning-only/non-claim and does not promote theorem/evidence status.

Cycle-011 adjudication posture transition (now pinned):
- adjudication token:
   - `SR_COVARIANCE_ADJUDICATION_v0: DISCHARGED_v0_PLANNING_CRITERIA_LOCKED_NONCLAIM`
- cycle token:
   - `SR_COVARIANCE_PROGRESS_CYCLE11_v0: ADJUDICATION_POSTURE_LOCK_TOKEN_PINNED`
- artifact token:
   - `SR_COVARIANCE_CYCLE11_ARTIFACT_v0: sr_covariance_adjudication_posture_cycle11_v0`
- artifact pointer:
   - `formal/output/sr_covariance_adjudication_posture_cycle11_v0.json`
- gate posture:
   - remains planning-only/non-claim and does not promote theorem/evidence status.

Non-claim boundary reinforcement:
- no claim of full special-relativistic dynamics completion.
- no claim of GR recovery from this target.
- no external truth claim.
