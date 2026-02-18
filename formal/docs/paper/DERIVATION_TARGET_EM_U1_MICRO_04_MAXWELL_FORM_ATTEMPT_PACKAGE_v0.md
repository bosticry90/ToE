# Derivation Target: EM U1 Micro-04 Maxwell-Form Attempt Package v0

Spec ID:
- `DERIVATION_TARGET_EM_U1_MICRO_04_MAXWELL_FORM_ATTEMPT_PACKAGE_v0`

Target ID:
- `TARGET-EM-U1-MICRO-04-MAXWELL-FORM-ATTEMPT-v0`

Classification:
- `P-POLICY`

Purpose:
- Define one dedicated artifact for bounded Maxwell-form attempt surfaces.
- Localize Maxwell-form expression scanning to this package after Cycle-003 authorization.
- Keep the attempt package planning-only and non-claim while enforcing shape-level contracts.

Adjudication token:
- `EM_U1_MICRO04_MAXWELL_FORM_ATTEMPT_ADJUDICATION: NOT_YET_DISCHARGED`

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

- Deliver one localized Maxwell-form attempt package under Cycle-003 authorization.
- Scope boundary is explicit and binding from this section onward:
  - bounded/non-claim Maxwell-form shape package only.

## ASSUMPTION FREEZE section

- Canonical assumption classes:
  - `MATH|DEF|POLICY|SCOPE`
- Authorization prerequisite token:
  - `EM_U1_MICRO03_PREDISCHARGE_GATE_BUNDLE_ADJUDICATION: DISCHARGED_CONDITIONAL_v0`
- Required differential-bundle registry assumptions:
  - `ASM-EM-U1-STR-01`
  - `ASM-EM-U1-SYM-01`

## CANONICAL_ROUTE section

- Maxwell-form shape expressions (planning-only, bounded):
  - `∇ · E = ρ`
  - `∇ × B = J + ∂E/∂t`
  - `∇ · B = 0`
  - `∇ × E = -∂B/∂t`
  - `∂_μ F^μν = J^ν`
  - `dF = 0`
- Dedicated artifact localization rule:
  - these shapes belong only to this Cycle-004 package while authorization is active.

## ANTI_SHORTCUT section

- Required anti-shortcut token:
  - `EM_U1_NO_SHORTCUT_GUARD_v0: OBJECT_ROUTE_REQUIRED`
- Forbidden shortcut:
  - promoting Maxwell-form shape presence into dynamics closure or discharge claims.

## COUNTERFACTUAL ROUTE section

- Counterfactual scaffold token:
  - `EM_U1_COUNTERFACTUAL_SCaffold_v0: REQUIRED_ASSUMPTION_REMOVAL_BREAKS_CLOSURE`
- If Cycle-003 authorization is not discharged, Maxwell-form shape presence must collapse to zero artifacts.

## INDEPENDENT NECESSITY ROUTE section

- Independent-necessity class token:
  - `EM_U1_INDEPENDENT_NECESSITY_CLASS_v0: OBJECT_CONSTRUCTIVE_ROUTE`
- Maxwell-form shapes remain theorem-surface placeholders, not closure claims.

## HARDENING section

- Cycle-004 hardening posture:
  - authorization-gated shape presence is machine-checked,
  - non-authorized state enforces shape absence,
  - shape localization is machine-checked against the Cycle-001/002/003 docs.
- Hardening scaffold token:
  - `EM_U1_HARDENING_SCAFFOLD_v0: ROBUSTNESS_NEGCTRL_TEMPLATES_PINNED`

## BOUNDED SCOPE section

- non-claim boundary is explicit and binding for this micro artifact.
- bounded Maxwell-form shape package scope only.
- no non-Abelian completion claim.
- no Standard Model completion claim.
- no external truth claim.

## DRIFT_GATES section

- Cycle-004 progress token:
  - `EM_U1_PROGRESS_CYCLE4_v0: MAXWELL_FORM_ATTEMPT_PACKAGE_TOKEN_PINNED`
- Shape gate token:
  - `EM_U1_MAXWELL_FORM_SHAPE_GATE_v0: AUTHORIZED_PRESENCE_ONLY`
- Localization gate token:
  - `EM_U1_MAXWELL_FORM_LOCALIZATION_GATE_v0: CYCLE4_ARTIFACT_ONLY`

## ADJUDICATION_SYNC section

- Cycle-004 adjudication token:
  - `EM_U1_MICRO04_MAXWELL_FORM_ATTEMPT_ADJUDICATION: NOT_YET_DISCHARGED`
- Canonical gate test pointer:
  - `formal/python/tests/test_em_u1_micro04_maxwell_form_attempt_shape.py`

Deliverable pointers:
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_03_PREDISCHARGE_GATE_BUNDLE_v0.md`
- `formal/python/tests/test_em_u1_micro04_maxwell_form_attempt_shape.py`
