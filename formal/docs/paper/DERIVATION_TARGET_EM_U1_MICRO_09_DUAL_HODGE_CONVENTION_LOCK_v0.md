# Derivation Target: EM U1 Micro-09 Dual/Hodge Convention Lock v0

Spec ID:
- `DERIVATION_TARGET_EM_U1_MICRO_09_DUAL_HODGE_CONVENTION_LOCK_v0`

Target ID:
- `TARGET-EM-U1-MICRO-09-DUAL-HODGE-CONVENTION-LOCK-v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze 4D dual/epsilon/Hodge conventions needed for unambiguous covariant EM notation.
- Keep this cycle planning-only/non-claim and non-dynamics.
- Provide typed operator seams for dual-field notation without selecting dynamics routes.

Adjudication token:
- `EM_U1_MICRO09_DUAL_HODGE_ADJUDICATION: NOT_YET_DISCHARGED`

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

- Deliver one bounded convention-lock artifact for:
  - Levi-Civita normalization/orientation choice,
  - Hodge-star sign convention under fixed signature,
  - dual-field definition seam for 2-form notation.
- Deliver one typed operator scaffold in Lean for:
  - epsilon convention placeholder,
  - Hodge-star placeholder operator,
  - dual-field placeholder definition.

## ASSUMPTION FREEZE section

- Canonical assumption classes:
  - `MATH|DEF|POLICY|SCOPE`
- Cycle-006 prerequisites remain fixed and referenced:
  - `EM_U1_CONVENTION_LOCK_SIGNATURE_v0: METRIC_SIGNATURE_FIXED`
  - `EM_U1_CONVENTION_LOCK_EB_v0: E_B_SIGN_AND_EPSILON_FIXED`
- New-physics assumption-ID policy remains unchanged:
  - `EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS`

## CANONICAL_ROUTE section

- Canonical convention route:
  - fix `epsilon` normalization and orientation declaration,
  - fix `hodgeStar2Form` convention declaration,
  - define `dualFieldStrength` as a typed placeholder seam from fixed conventions.
- Conventions are non-dynamics:
  - no equation-of-motion surfaces are declared.
  - no Maxwell-form derivation is attempted.
  - no source-coupled closure is attempted.

## ANTI_SHORTCUT section

- Required anti-shortcut token:
  - `EM_U1_NO_SHORTCUT_GUARD_v0: OBJECT_ROUTE_REQUIRED`
- Forbidden shortcuts:
  - introducing form-level source equation closures as claim content,
  - introducing covariant source-equation closures as claim content,
  - importing dynamics phrasing through dual/Hodge naming.

## COUNTERFACTUAL ROUTE section

- Counterfactual scaffold token:
  - `EM_U1_COUNTERFACTUAL_SCaffold_v0: REQUIRED_ASSUMPTION_REMOVAL_BREAKS_CLOSURE`
- If dual/Hodge conventions are left implicit, sign/orientation ambiguity can drift between tensor and form routes.

## INDEPENDENT NECESSITY ROUTE section

- Independent-necessity class token:
  - `EM_U1_INDEPENDENT_NECESSITY_CLASS_v0: OBJECT_CONSTRUCTIVE_ROUTE`
- Cycle-009 remains a convention-lock scaffold and does not alter theorem/discharge status.

## HARDENING section

- Cycle-009 hardening posture:
  - convention tokens must be explicit and synchronized across doc/Lean/state/target,
  - dual/Hodge/epsilon phrases are localized to Cycle-006 and Cycle-009 artifacts unless explicit localization token is present,
  - no-dynamics wording is mandatory in this artifact.
- Hardening scaffold token:
  - `EM_U1_HARDENING_SCAFFOLD_v0: ROBUSTNESS_NEGCTRL_TEMPLATES_PINNED`

## BOUNDED SCOPE section

- non-claim boundary is explicit and binding for this micro artifact.
- bounded dual/Hodge convention-lock scope only.
- no equation-of-motion claim.
- no Maxwell equation claim.
- no wave-equation claim.
- no Lagrangian claim.
- no constitutive closure claim.
- no unit-system selection claim.
- no gauge-fixing selection claim.
- no non-Abelian completion claim.
- no Standard Model completion claim.
- no external truth claim.

## DRIFT_GATES section

- Cycle-009 progress token:
  - `EM_U1_PROGRESS_CYCLE9_v0: DUAL_HODGE_CONVENTION_LOCK_TOKEN_PINNED`
- Dual-field convention token:
  - `EM_U1_DUAL_CONVENTION_v0: STARF_DEFINITION_FIXED`
- Epsilon convention token:
  - `EM_U1_EPSILON_CONVENTION_v0: LEVI_CIVITA_NORMALIZATION_FIXED`
- Hodge-star convention token:
  - `EM_U1_HODGE_STAR_CONVENTION_v0: STARSTAR_SIGN_FIXED_UNDER_SIGNATURE`
- Localization gate token:
  - `EM_U1_DUAL_HODGE_LOCALIZATION_GATE_v0: CYCLE6_CYCLE9_ARTIFACTS_ONLY`
- No-dynamics token:
  - `EM_U1_DUAL_HODGE_NO_DYNAMICS_v0: CONVENTION_LOCK_ONLY`

## ADJUDICATION_SYNC section

- Cycle-009 adjudication token:
  - `EM_U1_MICRO09_DUAL_HODGE_ADJUDICATION: NOT_YET_DISCHARGED`
- Canonical gate test pointer:
  - `formal/python/tests/test_em_u1_micro09_dual_hodge_convention_lock.py`

Deliverable pointers:
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_06_CONVENTION_LOCK_3P1_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md`
- `formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean`
- `formal/python/tests/test_em_u1_micro09_dual_hodge_convention_lock.py`
