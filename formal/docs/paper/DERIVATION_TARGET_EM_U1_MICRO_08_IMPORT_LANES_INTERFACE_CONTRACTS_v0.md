# Derivation Target: EM U1 Micro-08 Import Lanes Interface Contracts v0

Spec ID:
- `DERIVATION_TARGET_EM_U1_MICRO_08_IMPORT_LANES_INTERFACE_CONTRACTS_v0`

Target ID:
- `TARGET-EM-U1-MICRO-08-IMPORT-LANES-INTERFACE-CONTRACTS-v0`

Classification:
- `P-POLICY`

Purpose:
- Turn Cycle-007 import-lane placeholders into typed interface-contract seams.
- Keep this cycle planning-only/non-claim with no dynamics closure content.
- Prove import-lane references can be attached through explicit assumption-gated interfaces without selecting units or gauge.

Adjudication token:
- `EM_U1_MICRO08_IMPORT_LANES_INTERFACE_ADJUDICATION: NOT_YET_DISCHARGED`

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

- Deliver three typed import-lane interface contracts:
  - constitutive interface contract,
  - units interface contract,
  - gauge-fixing interface contract.
- Deliver one reference-only interface-application harness that attaches all three lanes with assumption-ID gating only.

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

- Canonical import-lane interface seams:
  - constitutive interface contract:
    - declares placeholder attachment points for `D,H,eps,mu` lanes only.
  - units interface contract:
    - declares placeholder attachment points for `SI`, `Gaussian`, `Heaviside-Lorentz`, and `c=1` lanes only.
  - gauge-fixing interface contract:
    - declares placeholder attachment points for `Lorenz`, `Coulomb`, `temporal`, `axial`, and `Feynman` lanes only.
- Interface seams are non-selecting:
  - no units convention is selected.
  - no gauge condition is selected.
  - no constitutive closure is selected.
- Interface seams are localized:
  - cycle-local references are restricted to Cycle-007 and Cycle-008 artifacts.

## ANTI_SHORTCUT section

- Required anti-shortcut token:
  - `EM_U1_NO_SHORTCUT_GUARD_v0: OBJECT_ROUTE_REQUIRED`
- Forbidden shortcut:
  - importing units/gauge/constitutive choices through interface language outside Cycle-007/08 artifacts.
  - promoting interface declarations as dynamics closure.

## COUNTERFACTUAL ROUTE section

- Counterfactual scaffold token:
  - `EM_U1_COUNTERFACTUAL_SCaffold_v0: REQUIRED_ASSUMPTION_REMOVAL_BREAKS_CLOSURE`
- If interface seams are not assumption-gated and localized, policy-level import controls can leak into non-authorized artifacts.

## INDEPENDENT NECESSITY ROUTE section

- Independent-necessity class token:
  - `EM_U1_INDEPENDENT_NECESSITY_CLASS_v0: OBJECT_CONSTRUCTIVE_ROUTE`
- Cycle-008 contributes typed attachment seams only and does not alter theorem/discharge status.

## HARDENING section

- Cycle-008 hardening posture:
  - three interface contracts must be present and assumption-gated,
  - no-selection token must be present,
  - import interface language must be localized to Cycle-007/08 artifacts,
  - interface-application harness must remain reference-only.
- Hardening scaffold token:
  - `EM_U1_HARDENING_SCAFFOLD_v0: ROBUSTNESS_NEGCTRL_TEMPLATES_PINNED`

## BOUNDED SCOPE section

- non-claim boundary is explicit and binding for this micro artifact.
- bounded interface-contract scope only.
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

- Cycle-008 progress token:
  - `EM_U1_PROGRESS_CYCLE8_v0: IMPORT_LANES_INTERFACE_CONTRACTS_TOKEN_PINNED`
- Interface-contract token:
  - `EM_U1_IMPORT_LANES_INTERFACE_CONTRACTS_v0: THREE_LANE_INTERFACES_DEFINED`
- No-selection token:
  - `EM_U1_IMPORT_LANES_INTERFACE_NO_SELECTION_v0: NO_UNITS_OR_GAUGE_SELECTION`
- Localization gate token:
  - `EM_U1_IMPORT_LANES_INTERFACE_LOCALIZATION_GATE_v0: CYCLE7_CYCLE8_ARTIFACTS_ONLY`
- Interface-application harness token:
  - `EM_U1_IMPORT_LANES_INTERFACE_APPLICATION_HARNESS_v0: REFERENCE_ONLY_IMPORT_APPLICATION`
- No-dynamics token:
  - `EM_U1_IMPORT_LANES_NO_DYNAMICS_v0: PLACEHOLDER_ONLY`
- New-physics ID gate token:
  - `EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS`

## ADJUDICATION_SYNC section

- Cycle-008 adjudication token:
  - `EM_U1_MICRO08_IMPORT_LANES_INTERFACE_ADJUDICATION: NOT_YET_DISCHARGED`
- Canonical gate test pointer:
  - `formal/python/tests/test_em_u1_micro08_import_lanes_interface_contracts.py`

Deliverable pointers:
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_07_IMPORT_LANES_PLACEHOLDERS_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md`
- `formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean`
- `formal/python/tests/test_em_u1_micro08_import_lanes_interface_contracts.py`
