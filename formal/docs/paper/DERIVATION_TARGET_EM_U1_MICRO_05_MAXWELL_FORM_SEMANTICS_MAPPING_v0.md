# Derivation Target: EM U1 Micro-05 Maxwell-Form Semantics Mapping v0

Spec ID:
- `DERIVATION_TARGET_EM_U1_MICRO_05_MAXWELL_FORM_SEMANTICS_MAPPING_v0`

Target ID:
- `TARGET-EM-U1-MICRO-05-MAXWELL-FORM-SEMANTICS-MAPPING-v0`

Classification:
- `P-POLICY`

Purpose:
- Define a bounded semantics-mapping layer between Cycle-004 Maxwell-form symbols and pinned EM object carriers.
- Keep the package strictly definitional/structural and non-claim.
- Enforce policy that any new-physics lane import requires explicit assumption IDs.

Adjudication token:
- `EM_U1_MICRO05_MAXWELL_FORM_SEMANTICS_MAPPING_ADJUDICATION: NOT_YET_DISCHARGED`

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

- Deliver one semantics-mapping package for Maxwell-form symbol interpretation.
- Scope boundary is explicit and binding from this section onward:
  - bounded/non-claim definitional mapping only.

## ASSUMPTION FREEZE section

- Canonical assumption classes:
  - `MATH|DEF|POLICY|SCOPE`
- Authorization prerequisite token:
  - `EM_U1_MICRO03_PREDISCHARGE_GATE_BUNDLE_ADJUDICATION: DISCHARGED_CONDITIONAL_v0`
- Mapping preconditions:
  - `FieldStrength` and `CurrentSource` carriers are pinned in `ObjectScaffold.lean`.
  - Cycle-004 shape package remains localized.

## CANONICAL_ROUTE section

- Definitional carrier mappings:
  - electric-symbol lane:
    - `E_i` maps to field-strength carrier components in the `F_{0i}` channel.
  - magnetic-symbol lane:
    - `B_k` maps to field-strength carrier components in antisymmetric spatial `F_{ij}` channels.
  - source-symbol lane:
    - `ρ` maps to current carrier component `J^0`.
    - `J_i` maps to current carrier spatial components `J^i`.
- Lean carrier pointer:
  - `formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean`

## ANTI_SHORTCUT section

- Required anti-shortcut token:
  - `EM_U1_NO_SHORTCUT_GUARD_v0: OBJECT_ROUTE_REQUIRED`
- Forbidden shortcut:
  - converting symbol-to-carrier mapping statements into dynamics closure claims.

## COUNTERFACTUAL ROUTE section

- Counterfactual scaffold token:
  - `EM_U1_COUNTERFACTUAL_SCaffold_v0: REQUIRED_ASSUMPTION_REMOVAL_BREAKS_CLOSURE`
- If carrier mapping is removed, Maxwell-form symbols lose object-consistent interpretation lane.

## INDEPENDENT NECESSITY ROUTE section

- Independent-necessity class token:
  - `EM_U1_INDEPENDENT_NECESSITY_CLASS_v0: OBJECT_CONSTRUCTIVE_ROUTE`
- This cycle remains mapping-only and does not change theorem status.

## HARDENING section

- Cycle-005 hardening posture:
  - mapping token presence is machine-checked,
  - localization to Cycle-004/Cycle-005 artifact boundaries is machine-checked,
  - non-physics import gate is machine-checked for required assumption IDs.
- Hardening scaffold token:
  - `EM_U1_HARDENING_SCAFFOLD_v0: ROBUSTNESS_NEGCTRL_TEMPLATES_PINNED`

## BOUNDED SCOPE section

- non-claim boundary is explicit and binding for this micro artifact.
- bounded semantics-mapping scope only.
- no dynamics closure claim.
- no constitutive-lane import claim.
- no unit-system fixation claim.
- no gauge-fixing import claim.
- no non-Abelian completion claim.
- no Standard Model completion claim.
- no external truth claim.

## DRIFT_GATES section

- Cycle-005 progress token:
  - `EM_U1_PROGRESS_CYCLE5_v0: MAXWELL_FORM_SEMANTICS_MAPPING_TOKEN_PINNED`
- Definitional-only gate token:
  - `EM_U1_MAXWELL_SEMANTICS_DEFINITIONAL_ONLY_GATE_v0: NO_DYNAMICS_CLOSURE_CLAIM`
- Carrier mapping tokens:
  - `EM_U1_MAXWELL_SEMANTICS_MAPPING_EB_v0: E_B_FROM_FIELD_STRENGTH_CARRIER_COMPONENTS`
  - `EM_U1_MAXWELL_SEMANTICS_MAPPING_RHOJ_v0: RHO_J_FROM_CURRENT_CARRIER_COMPONENTS`
- New-physics assumption-ID gate token:
  - `EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS`

## ADJUDICATION_SYNC section

- Cycle-005 adjudication token:
  - `EM_U1_MICRO05_MAXWELL_FORM_SEMANTICS_MAPPING_ADJUDICATION: NOT_YET_DISCHARGED`
- Canonical gate test pointer:
  - `formal/python/tests/test_em_u1_micro05_maxwell_form_semantics_mapping.py`

Deliverable pointers:
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_04_MAXWELL_FORM_ATTEMPT_PACKAGE_v0.md`
- `formal/python/tests/test_em_u1_micro05_maxwell_form_semantics_mapping.py`
