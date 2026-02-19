# Derivation Target: EM U1 Micro-19 Smoothness-Weakening Negcontrol v0

Spec ID:
- `DERIVATION_TARGET_EM_U1_MICRO_19_SMOOTHNESS_WEAKENING_NEGCONTROL_v0`

Target ID:
- `TARGET-EM-U1-MICRO-19-SMOOTHNESS-WEAKENING-NEGCONTROL-v0`

Classification:
- `P-POLICY`

Purpose:
- Pin one bounded negative-control package for the Maxwell-to-continuity route under smoothness weakening.
- Keep this cycle planning-only/non-claim with no theorem promotion or discharge claim.
- Localize one explicit failure-mode seam showing that removing the smoothness lane unlicenses the Cycle-018 theorem-attempt route.

Adjudication token:
- `EM_U1_MICRO19_SMOOTHNESS_NEGCONTROL_ADJUDICATION: NOT_YET_DISCHARGED`

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

- Deliver one bounded neg-control artifact that pins localized failure-mode seams:
  - `NEGCTRL_PREMISE_REMOVED: ASM-EM-U1-MATH-SMOOTH-01_WITHDRAWN`
  - `NEGCTRL_BREAKPOINT: COMMUTING_PARTIALS_ROUTE_UNLICENSED`
  - `NEGCTRL_OUTCOME: MAXWELL_TO_CONTINUITY_ATTEMPT_NOT_LICENSED`
- Deliver one typed neg-control harness seam in Lean for later theorem-attempt hardening lanes.
- Preserve neg-control-only posture with no theorem/discharge promotion.

## ASSUMPTION FREEZE section

- Canonical assumption classes:
  - `MATH|DEF|POLICY|SCOPE`
- Required source assumption ID:
  - `ASM-EM-U1-PHY-SOURCE-01`
- Referenced smoothness lane ID:
  - `ASM-EM-U1-MATH-SMOOTH-01`
- Required prerequisite chain tokens:
  - `EM_U1_MAXWELL_CONTINUITY_THEOREM_ROUTE_v0: DIVERGENCE_ANTISYM_COMMUTATION_ATTEMPT_PINNED`
  - `EM_U1_MAXWELL_CONTINUITY_THEOREM_SMOOTHNESS_SEAM_v0: C2_REGULARITY_REQUIRED`
  - `EM_U1_MAXWELL_CONTINUITY_ROUTE_v0: DIVERGENCE_OF_INHOM_SURFACE_ROUTE_PINNED`
  - `EM_U1_DOUBLE_DIVERGENCE_SURFACE_v0: DD_F_ZERO_STATEMENT_PINNED`
  - `EM_U1_COMMUTING_PARTIALS_SURFACE_v0: COMMUTATION_STATEMENT_PINNED`
- Required non-selection policy tokens:
  - `EM_U1_IMPORT_LANES_INTERFACE_NO_SELECTION_v0: NO_UNITS_OR_GAUGE_SELECTION`
  - `EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS`

## CANONICAL_ROUTE section

- Canonical neg-control route (single admissible skeleton in this cycle):
  - keep Cycle-018 theorem-attempt route tokens fixed as prerequisites,
  - withdraw the smoothness lane as a neg-control premise via `NEGCTRL_PREMISE_REMOVED`,
  - pin the route breakpoint `NEGCTRL_BREAKPOINT`,
  - pin the bounded endpoint `NEGCTRL_OUTCOME`.
- This cycle remains neg-control-only:
  - no theorem proof is asserted,
  - no discharge is asserted,
  - no promotion is asserted.

## ANTI_SHORTCUT section

- Required anti-shortcut token:
  - `EM_U1_NO_SHORTCUT_GUARD_v0: OBJECT_ROUTE_REQUIRED`
- Forbidden shortcuts:
  - claiming theorem-grade closure in this cycle,
  - importing singular-source/distributional lanes without a new explicit assumption-ID lane,
  - substituting curved-space divergence forms without a new explicit assumption-ID lane.

## COUNTERFACTUAL ROUTE section

- Counterfactual scaffold token:
  - `EM_U1_COUNTERFACTUAL_SCAFFOLD_v0: REQUIRED_ASSUMPTION_REMOVAL_BREAKS_CLOSURE`
- Without this neg-control package, smoothness-lane dependence can remain implicit and route licensing can drift.

## INDEPENDENT NECESSITY ROUTE section

- Independent-necessity class token:
  - `EM_U1_INDEPENDENT_NECESSITY_CLASS_v0: OBJECT_CONSTRUCTIVE_ROUTE`
- Cycle-019 remains structural-only and does not alter theorem/discharge status.

## HARDENING section

- Cycle-019 hardening posture:
  - neg-control tokens must be synchronized across doc/Lean/target/state/roadmap,
  - neg-control seam statements are localized to this cycle artifact,
  - theorem-promotion language is forbidden in this artifact.
- Hardening scaffold token:
  - `EM_U1_HARDENING_SCAFFOLD_v0: ROBUSTNESS_NEGCTRL_TEMPLATES_PINNED`

## BOUNDED_SCOPE section

- non-claim boundary is explicit and binding for this micro artifact.
- bounded smoothness-weakening neg-control scope only.
- no theorem proof claim.
- no theorem/discharge promotion claim.
- no route-closure claim.
- no singular-source/distributional formalization claim.
- no curved-space covariant-divergence claim.
- no unit-system selection claim.
- no gauge-fixing selection claim.
- no constitutive closure claim.
- no non-Abelian completion claim.
- no Standard Model completion claim.
- no external truth claim.

## DRIFT_GATES section

- Cycle-019 progress token:
  - `EM_U1_PROGRESS_CYCLE19_v0: SMOOTHNESS_WEAKENING_NEGCONTROL_TOKEN_PINNED`
- Neg-control route token:
  - `EM_U1_SMOOTHNESS_WEAKENING_NEGCONTROL_ROUTE_v0: COMMUTATION_LICENSE_REMOVAL_BREAKS_ROUTE_PINNED`
- Localization gate token:
  - `EM_U1_SMOOTHNESS_WEAKENING_NEGCONTROL_LOCALIZATION_GATE_v0: CYCLE19_ARTIFACTS_ONLY`
- No-promotion gate token:
  - `EM_U1_SMOOTHNESS_WEAKENING_NEGCONTROL_NO_PROMOTION_v0: NEGCONTROL_ONLY_NO_DISCHARGE`
- Boundary guard token:
  - `EM_U1_SMOOTHNESS_WEAKENING_NEGCONTROL_BOUNDARY_v0: NO_DISTRIBUTIONAL_OR_CURVED_SPACE_IMPORT`

## ADJUDICATION_SYNC section

- Cycle-019 adjudication token:
  - `EM_U1_MICRO19_SMOOTHNESS_NEGCONTROL_ADJUDICATION: NOT_YET_DISCHARGED`
- Canonical gate test pointer:
  - `formal/python/tests/test_em_u1_micro19_smoothness_weakening_negcontrol.py`

Deliverable pointers:
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_18_MAXWELL_TO_CONTINUITY_THEOREM_ATTEMPT_PACKAGE_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_16_MAXWELL_TO_CONTINUITY_ROUTE_ATTEMPT_PACKAGE_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_17_DOUBLE_DIVERGENCE_ANTISYM_COMMUTATION_SEAM_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md`
- `formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean`
- `formal/python/tests/test_em_u1_micro19_smoothness_weakening_negcontrol.py`
