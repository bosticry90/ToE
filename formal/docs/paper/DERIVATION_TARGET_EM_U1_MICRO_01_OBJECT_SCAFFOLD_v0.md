# Derivation Target: EM U1 Micro-01 Object Scaffold v0

Spec ID:
- `DERIVATION_TARGET_EM_U1_MICRO_01_OBJECT_SCAFFOLD_v0`

Target ID:
- `TARGET-EM-U1-MICRO-01-OBJECT-SCAFFOLD-v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze Cycle-001 object scaffold deliverables for EM U(1) under architecture-v1.
- Pin typed object surfaces and explicit assumption boundaries before any dynamics-layer closure attempts.
- Keep the lane bounded, non-claim, and anti-shortcut by construction.

Adjudication token:
- `EM_U1_MICRO01_OBJECT_SCAFFOLD_ADJUDICATION: NOT_YET_DISCHARGED`

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

- Deliver one typed object scaffold bundle:
  - gauge potential carrier (`A_mu`),
  - field-strength object carrier (`F_munu`),
  - current/source carrier (`J_mu`),
  - continuity assumption surface.

## ASSUMPTION FREEZE section

- Canonical assumption classes:
  - `MATH|DEF|POLICY|SCOPE`
- Assumption bundle token:
  - `EMU1Assumptions_v0`
- Continuity assumption is explicit and assumption-tagged in this cycle if not derived.

## CANONICAL ROUTE section

- Canonical object route:
  - `A_mu` object -> `F_munu` construction -> `J_mu` source object -> continuity assumption surface.
- Lean scaffold pointer:
  - `formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean`

## ANTI_SHORTCUT section

- Required anti-shortcut token:
  - `EM_U1_NO_SHORTCUT_GUARD_v0: OBJECT_ROUTE_REQUIRED`
- Forbidden in this artifact:
  - direct dynamics-layer closure claims,
  - implicit or hidden gauge-fixing assumptions.

## COUNTERFACTUAL ROUTE section

- Counterfactual scaffold token:
  - `EM_U1_COUNTERFACTUAL_SCaffold_v0: REQUIRED_ASSUMPTION_REMOVAL_BREAKS_CLOSURE`
- Removal of required object/continuity assumptions invalidates the Cycle-001 closure posture.

## INDEPENDENT NECESSITY ROUTE section

- Independent-necessity classification token:
  - `EM_U1_INDEPENDENT_NECESSITY_CLASS_v0: OBJECT_CONSTRUCTIVE_ROUTE`

## HARDENING section

- Cycle-001 hardening posture is structural:
  - object/token presence is machine-checked,
  - no equation-level dynamics claims are allowed.
- Hardening scaffold token:
  - `EM_U1_HARDENING_SCAFFOLD_v0: ROBUSTNESS_NEGCTRL_TEMPLATES_PINNED`

## BOUNDED SCOPE section

- non-claim boundary is explicit and binding for this micro artifact.
- bounded U(1) object scaffold scope only.
- no non-Abelian completion claim.
- no Standard Model completion claim.
- no external truth claim.

## DRIFT_GATES section

- Required drift gates:
  - object-route token must remain present,
  - assumption-bundle token must remain present and classed,
  - object scaffold must remain free of dynamics-equation forms.

## ADJUDICATION_SYNC section

- Cycle-001 progress token:
  - `EM_U1_PROGRESS_v0: CYCLE1_OBJECT_SCAFFOLD_TOKEN_PINNED`
- Cycle-001 adjudication token:
  - `EM_U1_MICRO01_OBJECT_SCAFFOLD_ADJUDICATION: NOT_YET_DISCHARGED`

Deliverable pointers:
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md`
- `formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean`
- `formal/python/tests/test_em_u1_micro01_template_and_tokens.py`
