# Derivation Target: EM U1 Micro-07 Import Lanes Placeholders v0

Spec ID:
- `DERIVATION_TARGET_EM_U1_MICRO_07_IMPORT_LANES_PLACEHOLDERS_v0`

Target ID:
- `TARGET-EM-U1-MICRO-07-IMPORT-LANES-PLACEHOLDERS-v0`

Classification:
- `P-POLICY`

Purpose:
- Define the only authorized placeholder lanes for future constitutive/units/gauge-fixing imports.
- Keep this cycle planning-only/non-claim with no dynamics closure content.
- Prevent silent import of SI/Gaussian, `ε0`/`μ0`, or gauge-fixing rules without explicit assumption IDs and localized artifacts.

Adjudication token:
- `EM_U1_MICRO07_IMPORT_LANES_ADJUDICATION: NOT_YET_DISCHARGED`

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

- Deliver one bounded placeholder artifact for import lanes only.
- Scope boundary is explicit and binding from this section onward:
  - bounded/non-claim placeholder-only import-lane control.

## ASSUMPTION FREEZE section

- Canonical assumption classes:
  - `MATH|DEF|POLICY|SCOPE`
- Required import-lane assumption IDs:
  - `ASM-EM-U1-PHY-CONSTITUTIVE-01`
  - `ASM-EM-U1-PHY-UNITS-01`
  - `ASM-EM-U1-PHY-GFIX-01`
- Required gate token:
  - `EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS`

## CANONICAL_ROUTE section

- Authorized placeholder lanes:
  - constitutive lane placeholders:
    - `D = ε E`, `B = μ H`, material-response placeholders only.
  - units lane placeholders:
    - SI units, Gaussian units, Heaviside-Lorentz, and `c = 1` mentions only as import-lane placeholders.
  - gauge-fixing lane placeholders:
    - Lorenz gauge, Coulomb gauge, temporal gauge, axial gauge, Feynman gauge mentions only as import-lane placeholders.
- Localization policy:
  - these lane mentions are localized to Cycle-007 placeholder artifacts until explicit promotion cycles authorize broader use.

## ANTI_SHORTCUT section

- Required anti-shortcut token:
  - `EM_U1_NO_SHORTCUT_GUARD_v0: OBJECT_ROUTE_REQUIRED`
- Forbidden shortcut:
  - importing constitutive/units/gauge-fixing language into other EM artifacts without explicit assumption IDs and localization gates.

## COUNTERFACTUAL ROUTE section

- Counterfactual scaffold token:
  - `EM_U1_COUNTERFACTUAL_SCaffold_v0: REQUIRED_ASSUMPTION_REMOVAL_BREAKS_CLOSURE`
- If import lanes are not explicitly localized and ID-gated, new-physics language can leak into dynamics-facing surfaces without policy control.

## INDEPENDENT NECESSITY ROUTE section

- Independent-necessity class token:
  - `EM_U1_INDEPENDENT_NECESSITY_CLASS_v0: OBJECT_CONSTRUCTIVE_ROUTE`
- This cycle remains import-lane scaffolding only and does not change theorem status.

## HARDENING section

- Cycle-007 hardening posture:
  - lane placeholder tokens are machine-checked,
  - localization to Cycle-007 artifact is machine-checked,
  - constitutive/units/gauge-fixing mentions require explicit assumption IDs.
- Hardening scaffold token:
  - `EM_U1_HARDENING_SCAFFOLD_v0: ROBUSTNESS_NEGCTRL_TEMPLATES_PINNED`

## BOUNDED SCOPE section

- non-claim boundary is explicit and binding for this micro artifact.
- bounded import-lane placeholder scope only.
- no equations-of-motion claim.
- no wave-equation claim.
- no Lagrangian claim.
- no constitutive closure claim.
- no unit-system selection claim.
- no gauge-fixing selection claim.
- no non-Abelian completion claim.
- no Standard Model completion claim.
- no external truth claim.

## DRIFT_GATES section

- Cycle-007 progress token:
  - `EM_U1_PROGRESS_CYCLE7_v0: IMPORT_LANES_PLACEHOLDERS_TOKEN_PINNED`
- Localization gate token:
  - `EM_U1_IMPORT_LANES_LOCALIZATION_GATE_v0: CONSTITUTIVE_UNITS_GFIXING_ONLY_IN_CYCLE7_ARTIFACTS`
- Placeholder-only gate token:
  - `EM_U1_IMPORT_LANES_NO_DYNAMICS_v0: PLACEHOLDER_ONLY`
- New-physics ID gate token:
  - `EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS`

## ADJUDICATION_SYNC section

- Cycle-007 adjudication token:
  - `EM_U1_MICRO07_IMPORT_LANES_ADJUDICATION: NOT_YET_DISCHARGED`
- Canonical gate test pointer:
  - `formal/python/tests/test_em_u1_micro07_import_lanes_placeholders.py`

Deliverable pointers:
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md`
- `formal/docs/paper/ASSUMPTION_REGISTRY_v1.md`
- `formal/python/tests/test_em_u1_micro07_import_lanes_placeholders.py`
