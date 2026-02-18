# Derivation Target: EM U1 Micro-02 Gauge-Contract Surface v0

Spec ID:
- `DERIVATION_TARGET_EM_U1_MICRO_02_GAUGE_CONTRACT_SURFACE_v0`

Target ID:
- `TARGET-EM-U1-MICRO-02-GAUGE-CONTRACT-SURFACE-v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze Cycle-002 gauge-contract theorem-surface scaffolding under architecture-v1.
- Upgrade field-strength gauge invariance from tautological assumption forwarding to derivation under explicit differential-bundle assumptions.
- Preserve bounded/non-claim posture without importing dynamics-layer closure.

Adjudication token:
- `EM_U1_MICRO02_GAUGE_CONTRACT_SURFACE_ADJUDICATION: NOT_YET_DISCHARGED`

## Architecture phase coverage (v1)

- `TARGET_DEFINITION`
- `ASSUMPTION_FREEZE`
- `CANONICAL_ROUTE`
- `ANTI_SHORTCUT`
- `COUNTERFACTUAL`
- `INDEPENDENT_NECESSITY`
- `HARDENING`
- `BOUNDED_SCOPE`
- `DRIFT_GATES`
- `ADJUDICATION_SYNC`

## TARGET section

- Deliver a theorem-surface gauge-contract scaffold that derives `F_munu` invariance under explicit assumptions.
- Do not introduce Maxwell-equation-form dynamics claims in this cycle.

## ASSUMPTION FREEZE section

- Canonical assumption classes:
  - `MATH|DEF|POLICY|SCOPE`
- Differential-bundle assumption surface token:
  - `EM_U1_GAUGE_CONTRACT_ASSUMPTION_SURFACE_v0: COMMUTATIVITY_LINEARITY_PINNED`
- Required assumptions for Cycle-002 theorem route:
  - partial-vector additivity over componentwise sums,
  - scalar second-partial commutativity on the gauge scalar carrier.

## CANONICAL ROUTE section

- Canonical theorem route:
  - `A_mu -> A_mu + dχ` gauge action,
  - `F_munu` antisymmetric construction from partial operators,
  - cancellation of gauge increment terms via commutativity assumption.
- Lean pointer:
  - `formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean`

## ANTI_SHORTCUT section

- Required anti-shortcut token:
  - `EM_U1_NO_SHORTCUT_GUARD_v0: OBJECT_ROUTE_REQUIRED`
- Forbidden shortcut:
  - assuming gauge invariance directly as theorem input.

## COUNTERFACTUAL ROUTE section

- Counterfactual scaffold token:
  - `EM_U1_COUNTERFACTUAL_SCaffold_v0: REQUIRED_ASSUMPTION_REMOVAL_BREAKS_CLOSURE`
- If additivity/commutativity assumptions are removed, gauge-contract closure is not derivable in this cycle.

## INDEPENDENT NECESSITY ROUTE section

- Independent-necessity class token:
  - `EM_U1_INDEPENDENT_NECESSITY_CLASS_v0: OBJECT_CONSTRUCTIVE_ROUTE`
- Route remains theorem-object constrained and non-circular.

## HARDENING section

- Cycle-002 hardening posture:
  - theorem-surface shape and token presence are machine-checked,
  - anti-tautology requirement is enforced by gate tests.
- Hardening scaffold token:
  - `EM_U1_HARDENING_SCAFFOLD_v0: ROBUSTNESS_NEGCTRL_TEMPLATES_PINNED`

## BOUNDED SCOPE section

- non-claim boundary is explicit and binding for this micro artifact.
- bounded gauge-contract theorem-surface scope only.
- no non-Abelian completion claim.
- no Standard Model completion claim.
- no external truth claim.

## DRIFT_GATES section

- Required drift gates:
  - Cycle-002 theorem must remain assumption-derived (not tautological),
  - assumption-surface token must remain explicit,
  - no Maxwell-equation-form expressions in this micro artifact.

## ADJUDICATION_SYNC section

- Cycle-002 progress token:
  - `EM_U1_PROGRESS_CYCLE2_v0: GAUGE_CONTRACT_SURFACE_TOKEN_PINNED`
- Cycle-002 derivation token:
  - `EM_U1_GAUGE_CONTRACT_DERIVATION_TOKEN_v0: FIELD_STRENGTH_INVARIANCE_FROM_DIFFERENTIAL_BUNDLE_ASSUMPTIONS`
- Cycle-002 adjudication token:
  - `EM_U1_MICRO02_GAUGE_CONTRACT_SURFACE_ADJUDICATION: NOT_YET_DISCHARGED`

Deliverable pointers:
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md`
- `formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean`
- `formal/python/tests/test_em_u1_micro02_gauge_contract_surface.py`
