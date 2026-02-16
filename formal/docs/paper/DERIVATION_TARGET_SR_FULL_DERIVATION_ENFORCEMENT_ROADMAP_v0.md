# Derivation Target: SR Full-Derivation Enforcement Roadmap v0

Spec ID:
- `DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0`

Target ID:
- `TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN`

Classification:
- `P-POLICY`

Purpose:
- Pin an authoritative, no-deviation execution roadmap to reach SR full derivation/discharge/inevitability.
- Prevent lane drift from prior proven governance sequence discipline.
- Enforce phase order, promotion gates, and reopen triggers under explicit non-claim boundaries.

Adjudication token:
- `SR_FULL_DERIVATION_ENFORCEMENT_ADJUDICATION: DISCHARGED_v0_ROADMAP_PINNED`

Non-claim boundary:
- planning-only enforcement control surface.
- does not promote claim labels by itself.
- no full SR dynamics derivation claim by itself.
- no inevitability claim by itself.
- no external truth claim.

## Authoritative no-deviation rule

- Execute phases strictly in order; no phase-skip promotion is allowed.
- Promotion tokens may be pinned early, but claim promotion is forbidden until all upstream discharge gates are satisfied.
- Any regression in canonical tokens, robustness/negative-control surfaces, or theorem-object consistency reopens the lane.

## Mandatory phase order (authoritative)

### Phase I — Theorem-object realization

- Required objects:
  - Lorentz transform object theorem surface.
  - interval-invariance preservation theorem surface.
  - velocity-composition closure theorem surface.
  - covariance contract theorem surface.
- Required artifact lane:
  - `formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean` (stub) followed by discharge-grade theorem replacements.

### Phase II — Canonical equivalence theorem

- Required theorem-level equivalence surface to canonical SR covariance/kinematics form under bounded assumptions.
- Narrative-only equivalence mapping is insufficient.

### Phase III — Assumption minimization discharge

- Required assumption classes: `MATH|DEF|POLICY|SCOPE`.
- Removable assumptions must be discharged or retained with explicit theorem-linked rationale.

### Phase IV — Robustness + negative-control discharge

- Robustness and negative-control families must be theorem-linked, artifact-pinned, and failure-informative.
- Family completion token is necessary but not sufficient without theorem-object linkage.

### Phase V — Derivation-completeness gate discharge

- `TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN` must move from scaffold/open posture to discharge-ready closure posture.
- Mandatory failure-trigger checks must all be satisfied.

### Phase VI — Inevitability gate discharge

- Necessity theorem required: minimized assumptions imply SR structure.
- Counterfactual negative controls required: removing required assumptions invalidates the SR conclusion.
- Inevitability scope must remain bounded and explicitly declared.

### Phase VII — Package freeze and reopen policy

- Freeze token pinning required for publication package.
- Reopen triggers required for token drift, theorem-regression, robustness/negative-control regression, and scope drift.

## Promotion gates

- `TOE-SR-THM-01` remains non-promotable beyond scaffold conditional posture until Phases I–V are discharged.
- Full-derivation/discharge wording remains forbidden until Phase V is discharged.
- Inevitability wording remains forbidden until Phase VI is discharged.

## Canonical synchronization surfaces

- `formal/docs/paper/DERIVATION_TARGET_SR_COVARIANCE_OBJECT_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_SR_COVARIANCE_THEOREM_SURFACE_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_SR_DERIVATION_COMPLETENESS_GATE_v0.md`
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `formal/docs/paper/RESULTS_TABLE_v0.md`
- `State_of_the_Theory.md`

## Enforcement hooks

- `formal/python/tests/test_sr_covariance_kickoff_gate.py`
- `formal/python/tests/test_sr_theorem_surface_scaffold_gate.py`
- `formal/python/tests/test_sr_full_derivation_enforcement_roadmap_gate.py`
