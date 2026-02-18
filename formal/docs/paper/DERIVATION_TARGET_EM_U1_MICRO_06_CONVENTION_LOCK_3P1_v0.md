# Derivation Target: EM U1 Micro-06 Convention Lock 3+1 v0

Spec ID:
- `DERIVATION_TARGET_EM_U1_MICRO_06_CONVENTION_LOCK_3P1_v0`

Target ID:
- `TARGET-EM-U1-MICRO-06-CONVENTION-LOCK-3P1-v0`

Classification:
- `P-POLICY`

Purpose:
- Lock 3+1 split, sign, index, and orientation conventions needed to make Cycle-005 semantics mapping unambiguous.
- Keep this cycle purely definitional/structural and non-claim.
- Prevent silent convention drift before any later dynamics-facing work.

Adjudication token:
- `EM_U1_MICRO06_CONVENTION_LOCK_3P1_ADJUDICATION: NOT_YET_DISCHARGED`

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

- Deliver one explicit convention lock package for EM symbol/object mapping consistency.
- Scope boundary is explicit and binding from this section onward:
  - bounded/non-claim convention lock only.

## ASSUMPTION FREEZE section

- Canonical assumption classes:
  - `MATH|DEF|POLICY|SCOPE`
- Required carry-through gate token:
  - `EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS`
- Authorization prerequisite:
  - `EM_U1_MICRO03_PREDISCHARGE_GATE_BUNDLE_ADJUDICATION: DISCHARGED_CONDITIONAL_v0`

## CANONICAL_ROUTE section

- Fixed metric-signature convention:
  - `(-,+,+,+)`
  - token: `EM_U1_CONVENTION_LOCK_SIGNATURE_v0: METRIC_SIGNATURE_FIXED`
- Fixed index-position convention:
  - index lowering uses `g_{μν}`,
  - index raising uses `g^{μν}`,
  - token: `EM_U1_CONVENTION_LOCK_INDEX_v0: INDEX_POSITION_RULES_FIXED`
- Fixed `E/B` split convention:
  - `E_i := F_{0i}`,
  - `F_{ij} := - ε_{ijk} B^k`,
  - spatial Levi-Civita orientation convention:
    - `ε^{0123} = +1`,
  - token: `EM_U1_CONVENTION_LOCK_EB_v0: E_B_SIGN_AND_EPSILON_FIXED`
- Units policy convention:
  - no unit-system selection in this cycle,
  - token: `EM_U1_CONVENTION_LOCK_UNITS_POLICY_v0: UNITS_NOT_SELECTED`

## ANTI_SHORTCUT section

- Required anti-shortcut token:
  - `EM_U1_NO_SHORTCUT_GUARD_v0: OBJECT_ROUTE_REQUIRED`
- Forbidden shortcut:
  - treating convention lock as dynamics derivation or closure.

## COUNTERFACTUAL ROUTE section

- Counterfactual scaffold token:
  - `EM_U1_COUNTERFACTUAL_SCaffold_v0: REQUIRED_ASSUMPTION_REMOVAL_BREAKS_CLOSURE`
- If sign/index/orientation conventions are not fixed, Cycle-005 mappings are ambiguous and drift-prone.

## INDEPENDENT NECESSITY ROUTE section

- Independent-necessity class token:
  - `EM_U1_INDEPENDENT_NECESSITY_CLASS_v0: OBJECT_CONSTRUCTIVE_ROUTE`
- Convention lock remains structural and non-promotional.

## HARDENING section

- Cycle-006 hardening posture:
  - fixed signature/index/`E/B` conventions are machine-checked,
  - definitional-only posture is machine-checked,
  - units/constitutive/gauge-fixing import without assumption IDs is blocked.
- Hardening scaffold token:
  - `EM_U1_HARDENING_SCAFFOLD_v0: ROBUSTNESS_NEGCTRL_TEMPLATES_PINNED`

## BOUNDED SCOPE section

- non-claim boundary is explicit and binding for this micro artifact.
- bounded convention-lock scope only.
- no dynamics derivation claim.
- no constitutive-lane import claim.
- no unit-system selection claim.
- no gauge-fixing import claim.
- no non-Abelian completion claim.
- no Standard Model completion claim.
- no external truth claim.

## DRIFT_GATES section

- Cycle-006 progress token:
  - `EM_U1_PROGRESS_CYCLE6_v0: CONVENTION_LOCK_3P1_TOKEN_PINNED`
- Definitional-only token:
  - `EM_U1_CONVENTION_LOCK_NO_DYNAMICS_v0: DEFINITIONAL_ONLY`
- Signature/index/`E/B` lock tokens:
  - `EM_U1_CONVENTION_LOCK_SIGNATURE_v0: METRIC_SIGNATURE_FIXED`
  - `EM_U1_CONVENTION_LOCK_INDEX_v0: INDEX_POSITION_RULES_FIXED`
  - `EM_U1_CONVENTION_LOCK_EB_v0: E_B_SIGN_AND_EPSILON_FIXED`
  - `EM_U1_CONVENTION_LOCK_UNITS_POLICY_v0: UNITS_NOT_SELECTED`
- New-physics assumption-ID gate token:
  - `EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS`

## ADJUDICATION_SYNC section

- Cycle-006 adjudication token:
  - `EM_U1_MICRO06_CONVENTION_LOCK_3P1_ADJUDICATION: NOT_YET_DISCHARGED`
- Canonical gate test pointer:
  - `formal/python/tests/test_em_u1_micro06_convention_lock_3p1.py`

Deliverable pointers:
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_05_MAXWELL_FORM_SEMANTICS_MAPPING_v0.md`
- `formal/python/tests/test_em_u1_micro06_convention_lock_3p1.py`
