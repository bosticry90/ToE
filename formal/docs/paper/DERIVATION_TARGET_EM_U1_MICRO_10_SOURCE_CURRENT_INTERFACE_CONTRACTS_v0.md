# Derivation Target: EM U1 Micro-10 Source/Current Interface Contracts v0

Spec ID:
- `DERIVATION_TARGET_EM_U1_MICRO_10_SOURCE_CURRENT_INTERFACE_CONTRACTS_v0`

Target ID:
- `TARGET-EM-U1-MICRO-10-SOURCE-CURRENT-INTERFACE-CONTRACTS-v0`

Classification:
- `P-POLICY`

Purpose:
- Define typed source/current interface seams required for later bounded Maxwell-form attempts.
- Keep this cycle planning-only/non-claim and non-dynamics.
- Freeze source-object conventions without asserting source equations as laws.

Adjudication token:
- `EM_U1_MICRO10_SOURCE_CURRENT_ADJUDICATION: NOT_YET_DISCHARGED`

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

- Deliver three bounded source/current interface seams:
  - covariant current object seam,
  - `rho/j` split seam under fixed 3+1 conventions,
  - continuity predicate seam as optional interface constraint only.
- Deliver one reference-only source-interface harness for assumption-ID-gated attachment.

## ASSUMPTION FREEZE section

- Canonical assumption classes:
  - `MATH|DEF|POLICY|SCOPE`
- Required source assumption ID:
  - `ASM-EM-U1-PHY-SOURCE-01`
- Required gate token:
  - `EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS`
- Required convention prerequisites:
  - `EM_U1_CONVENTION_LOCK_SIGNATURE_v0: METRIC_SIGNATURE_FIXED`
  - `EM_U1_CONVENTION_LOCK_EB_v0: E_B_SIGN_AND_EPSILON_FIXED`

## CANONICAL_ROUTE section

- Canonical source route:
  - define `CovariantCurrent` as a typed placeholder object seam,
  - define `SourceSplitInterface` as a typed `rho/j` mapping seam,
  - define `continuityPredicate` as optional interface constraint only.
- Source seam is non-dynamics:
  - no source equation is promoted as law in this cycle,
  - no Maxwell-form source closure is attempted in this cycle.

## ANTI_SHORTCUT section

- Required anti-shortcut token:
  - `EM_U1_NO_SHORTCUT_GUARD_v0: OBJECT_ROUTE_REQUIRED`
- Forbidden shortcuts:
  - treating continuity predicate seam as a derived dynamics law,
  - importing source-equation closures through interface wording,
  - bypassing source assumption-ID gating.

## COUNTERFACTUAL ROUTE section

- Counterfactual scaffold token:
  - `EM_U1_COUNTERFACTUAL_SCaffold_v0: REQUIRED_ASSUMPTION_REMOVAL_BREAKS_CLOSURE`
- Without a frozen source/current seam, later tensor/forms routes can drift in source object semantics.

## INDEPENDENT NECESSITY ROUTE section

- Independent-necessity class token:
  - `EM_U1_INDEPENDENT_NECESSITY_CLASS_v0: OBJECT_CONSTRUCTIVE_ROUTE`
- Cycle-010 remains structural-only and does not alter theorem/discharge status.

## HARDENING section

- Cycle-010 hardening posture:
  - source/current tokens must be synchronized across doc/Lean/target/state/roadmap,
  - source/current phrase usage is localized to Cycle-010 artifacts unless explicit localization token appears,
  - dynamics/equation forms remain forbidden in this artifact.
- Hardening scaffold token:
  - `EM_U1_HARDENING_SCAFFOLD_v0: ROBUSTNESS_NEGCTRL_TEMPLATES_PINNED`

## BOUNDED_SCOPE section

- non-claim boundary is explicit and binding for this micro artifact.
- bounded source/current interface-contract scope only.
- no source equation law claim.
- no Maxwell equation claim.
- no wave-equation claim.
- no Lagrangian claim.
- no non-Abelian completion claim.
- no Standard Model completion claim.
- no external truth claim.

## DRIFT_GATES section

- Cycle-010 progress token:
  - `EM_U1_PROGRESS_CYCLE10_v0: SOURCE_CURRENT_INTERFACE_TOKEN_PINNED`
- Source object convention token:
  - `EM_U1_SOURCE_OBJECT_CONVENTION_v0: CURRENT_OBJECT_DEFINED`
- Source split convention token:
  - `EM_U1_SOURCE_SPLIT_CONVENTION_v0: RHO_J_SPLIT_SEAM_DEFINED`
- Continuity predicate token:
  - `EM_U1_SOURCE_CONTINUITY_PREDICATE_v0: OPTIONAL_INTERFACE_CONSTRAINT_ONLY`
- Localization gate token:
  - `EM_U1_SOURCE_LOCALIZATION_GATE_v0: CYCLE10_ARTIFACTS_ONLY`
- No-dynamics token:
  - `EM_U1_SOURCE_NO_DYNAMICS_v0: INTERFACE_ONLY`

## ADJUDICATION_SYNC section

- Cycle-010 adjudication token:
  - `EM_U1_MICRO10_SOURCE_CURRENT_ADJUDICATION: NOT_YET_DISCHARGED`
- Canonical gate test pointer:
  - `formal/python/tests/test_em_u1_micro10_source_current_interface_contracts.py`

Deliverable pointers:
- `formal/docs/paper/ASSUMPTION_REGISTRY_v1.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md`
- `formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean`
- `formal/python/tests/test_em_u1_micro10_source_current_interface_contracts.py`
