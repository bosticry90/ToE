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

Non-claim boundary reinforcement:
- no claim of full special-relativistic dynamics completion.
- no claim of GR recovery from this target.
- no external truth claim.
