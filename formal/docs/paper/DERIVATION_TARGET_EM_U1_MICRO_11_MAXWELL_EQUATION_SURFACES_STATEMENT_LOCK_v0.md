# Derivation Target: EM U1 Micro-11 Maxwell Equation Surfaces Statement Lock v0

Spec ID:
- `DERIVATION_TARGET_EM_U1_MICRO_11_MAXWELL_EQUATION_SURFACES_STATEMENT_LOCK_v0`

Target ID:
- `TARGET-EM-U1-MICRO-11-MAXWELL-EQUATION-SURFACES-STATEMENT-LOCK-v0`

Classification:
- `P-POLICY`

Purpose:
- Pin Maxwell equation statement surfaces in tensor and forms notation under frozen EM conventions.
- Keep this cycle planning-only/non-claim and statement-only.
- Prevent derivation/promotion language drift while preserving localized statement artifacts.

Adjudication token:
- `EM_U1_MICRO11_MAXWELL_SURFACES_ADJUDICATION: NOT_YET_DISCHARGED`

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

- Deliver one bounded statement-lock artifact for Maxwell equation surfaces in two notations:
  - tensor statement surfaces,
  - forms statement surfaces.
- Keep equation presence localized and explicitly non-derivational in this cycle.

## ASSUMPTION FREEZE section

- Canonical assumption classes:
  - `MATH|DEF|POLICY|SCOPE`
- Required source assumption ID:
  - `ASM-EM-U1-PHY-SOURCE-01`
- Required convention/source prerequisite tokens:
  - `EM_U1_CONVENTION_LOCK_SIGNATURE_v0: METRIC_SIGNATURE_FIXED`
  - `EM_U1_HODGE_STAR_CONVENTION_v0: STARSTAR_SIGN_FIXED_UNDER_SIGNATURE`
  - `EM_U1_SOURCE_OBJECT_CONVENTION_v0: CURRENT_OBJECT_DEFINED`
- Non-selection constraints remain active:
  - `EM_U1_IMPORT_LANES_INTERFACE_NO_SELECTION_v0: NO_UNITS_OR_GAUGE_SELECTION`
  - `EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS`

## CANONICAL_ROUTE section

- Canonical statement route:
  - pin tensor Maxwell statement surfaces as statement-only forms:
    - `∂_μ F^{μν} = J^ν`
    - `∂_[α F_{βγ]} = 0`
  - pin forms Maxwell statement surfaces as statement-only forms:
    - `dF = 0`
    - `d⋆F = J`
- This cycle is statement-only:
  - no derivation is asserted,
  - no promotion/discharge is asserted,
  - no dynamics-closure claim is asserted.

## ANTI_SHORTCUT section

- Required anti-shortcut token:
  - `EM_U1_NO_SHORTCUT_GUARD_v0: OBJECT_ROUTE_REQUIRED`
- Forbidden shortcuts:
  - using equation statements as proof/discharge evidence,
  - derivation-language promotion from statement-only surfaces,
  - introducing units/constitutive/gauge-fixing selections via statement wording.

## COUNTERFACTUAL ROUTE section

- Counterfactual scaffold token:
  - `EM_U1_COUNTERFACTUAL_SCaffold_v0: REQUIRED_ASSUMPTION_REMOVAL_BREAKS_CLOSURE`
- Without a statement-lock layer, notation surfaces can drift between Cycle-004 attempt packaging and later theorem-target work.

## INDEPENDENT NECESSITY ROUTE section

- Independent-necessity class token:
  - `EM_U1_INDEPENDENT_NECESSITY_CLASS_v0: OBJECT_CONSTRUCTIVE_ROUTE`
- Cycle-011 remains structural-only and does not alter theorem/discharge status.

## HARDENING section

- Cycle-011 hardening posture:
  - statement tokens must be synchronized across doc/Lean/target/state/roadmap,
  - Maxwell statement phrases are localized to authorized EM artifacts,
  - derivation/promotion wording is forbidden in this artifact.
- Hardening scaffold token:
  - `EM_U1_HARDENING_SCAFFOLD_v0: ROBUSTNESS_NEGCTRL_TEMPLATES_PINNED`

## BOUNDED_SCOPE section

- non-claim boundary is explicit and binding for this micro artifact.
- bounded statement-surface lock only.
- no derivation claim.
- no theorem/discharge promotion claim.
- no wave-equation claim.
- no Lagrangian claim.
- no constitutive closure claim.
- no unit-system selection claim.
- no gauge-fixing selection claim.
- no non-Abelian completion claim.
- no Standard Model completion claim.
- no external truth claim.

## DRIFT_GATES section

- Cycle-011 progress token:
  - `EM_U1_PROGRESS_CYCLE11_v0: MAXWELL_EQUATION_SURFACES_TOKEN_PINNED`
- Tensor statement-surface token:
  - `EM_U1_MAXWELL_TENSOR_SURFACE_v0: INHOM_HOM_STATEMENTS_PINNED`
- Forms statement-surface token:
  - `EM_U1_MAXWELL_FORMS_SURFACE_v0: DUAL_HODGE_DEPENDENT_STATEMENTS_PINNED`
- Localization gate token:
  - `EM_U1_MAXWELL_SURFACE_LOCALIZATION_GATE_v0: CYCLE11_ARTIFACTS_ONLY`
- No-derivation gate token:
  - `EM_U1_MAXWELL_SURFACE_NO_DERIVATION_v0: STATEMENT_ONLY`

## ADJUDICATION_SYNC section

- Cycle-011 adjudication token:
  - `EM_U1_MICRO11_MAXWELL_SURFACES_ADJUDICATION: NOT_YET_DISCHARGED`
- Canonical gate test pointer:
  - `formal/python/tests/test_em_u1_micro11_maxwell_equation_surfaces_statement_lock.py`

Deliverable pointers:
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_04_MAXWELL_FORM_ATTEMPT_PACKAGE_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md`
- `formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean`
- `formal/python/tests/test_em_u1_micro11_maxwell_equation_surfaces_statement_lock.py`
