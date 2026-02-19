# Derivation Target: EM U1 Micro-13 Maxwell Tensor/Forms Compatibility Map v0

Spec ID:
- `DERIVATION_TARGET_EM_U1_MICRO_13_MAXWELL_TENSOR_FORMS_COMPATIBILITY_MAP_v0`

Target ID:
- `TARGET-EM-U1-MICRO-13-MAXWELL-TENSOR-FORMS-COMPATIBILITY-MAP-v0`

Classification:
- `P-POLICY`

Purpose:
- Pin a statement-only compatibility map between tensor and forms Maxwell statement surfaces.
- Keep this cycle planning-only/non-claim with no derivation or promotion language.
- Bind the map explicitly to frozen convention/source prerequisites.

Adjudication token:
- `EM_U1_MICRO13_MAXWELL_COMPATIBILITY_ADJUDICATION: NOT_YET_DISCHARGED`

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

- Deliver one bounded compatibility-map artifact that pins statement-surface translation only:
  - `∂_μ F^{μν} = J^ν ↔ d⋆F = J`
  - `∂_[α F_{βγ]} = 0 ↔ dF = 0`
- Deliver one typed compatibility harness seam in Lean for later theorem-route attachment.
- Preserve statement-only posture with no derivation assertions.

## ASSUMPTION FREEZE section

- Canonical assumption classes:
  - `MATH|DEF|POLICY|SCOPE`
- Required source assumption ID:
  - `ASM-EM-U1-PHY-SOURCE-01`
- Required convention/source prerequisite tokens:
  - `EM_U1_CONVENTION_LOCK_SIGNATURE_v0: METRIC_SIGNATURE_FIXED`
  - `EM_U1_HODGE_STAR_CONVENTION_v0: STARSTAR_SIGN_FIXED_UNDER_SIGNATURE`
  - `EM_U1_CONVENTION_LOCK_EB_v0: E_B_SIGN_AND_EPSILON_FIXED`
  - `EM_U1_SOURCE_OBJECT_CONVENTION_v0: CURRENT_OBJECT_DEFINED`
- Non-selection policy remains active:
  - `EM_U1_IMPORT_LANES_INTERFACE_NO_SELECTION_v0: NO_UNITS_OR_GAUGE_SELECTION`
  - `EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS`

## CANONICAL_ROUTE section

- Canonical compatibility route:
  - reference Cycle-011 tensor/forms statement surfaces,
  - reference Cycle-012 A↔F bridge seam and Cycle-009 dual/Hodge lock,
  - pin bidirectional statement-surface translation tags only.
- This cycle is statement-only:
  - no implication proof is asserted,
  - no derivation from gauge invariance is asserted,
  - no theorem discharge/promotion is asserted.

## ANTI_SHORTCUT section

- Required anti-shortcut token:
  - `EM_U1_NO_SHORTCUT_GUARD_v0: OBJECT_ROUTE_REQUIRED`
- Forbidden shortcuts:
  - elevating compatibility-map tags into proof/discharge claims,
  - introducing units/constitutive/gauge-fixing selections through map wording,
  - importing derivation language into this statement-only cycle.

## COUNTERFACTUAL ROUTE section

- Counterfactual scaffold token:
  - `EM_U1_COUNTERFACTUAL_SCaffold_v0: REQUIRED_ASSUMPTION_REMOVAL_BREAKS_CLOSURE`
- Without a pinned tensor↔forms compatibility map, statement surfaces can drift between notation lanes and reopen convention ambiguity.

## INDEPENDENT NECESSITY ROUTE section

- Independent-necessity class token:
  - `EM_U1_INDEPENDENT_NECESSITY_CLASS_v0: OBJECT_CONSTRUCTIVE_ROUTE`
- Cycle-013 remains structural-only and does not alter theorem/discharge status.

## HARDENING section

- Cycle-013 hardening posture:
  - compatibility-map tokens must be synchronized across doc/Lean/target/state/roadmap,
  - explicit equation-map phrases are localized to this cycle artifact,
  - derivation/promotion language is forbidden in this artifact.
- Hardening scaffold token:
  - `EM_U1_HARDENING_SCAFFOLD_v0: ROBUSTNESS_NEGCTRL_TEMPLATES_PINNED`

## BOUNDED_SCOPE section

- non-claim boundary is explicit and binding for this micro artifact.
- bounded Maxwell tensor/forms compatibility-map scope only.
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

- Cycle-013 progress token:
  - `EM_U1_PROGRESS_CYCLE13_v0: MAXWELL_COMPATIBILITY_MAP_TOKEN_PINNED`
- Compatibility-map token:
  - `EM_U1_MAXWELL_TENSOR_FORMS_MAP_v0: STATEMENT_SURFACE_TRANSLATION_PINNED`
- Localization gate token:
  - `EM_U1_MAXWELL_COMPATIBILITY_LOCALIZATION_GATE_v0: CYCLE13_ARTIFACTS_ONLY`
- No-derivation gate token:
  - `EM_U1_MAXWELL_COMPATIBILITY_NO_DERIVATION_v0: STATEMENT_ONLY`

## ADJUDICATION_SYNC section

- Cycle-013 adjudication token:
  - `EM_U1_MICRO13_MAXWELL_COMPATIBILITY_ADJUDICATION: NOT_YET_DISCHARGED`
- Canonical gate test pointer:
  - `formal/python/tests/test_em_u1_micro13_maxwell_tensor_forms_compatibility_map.py`

Deliverable pointers:
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_11_MAXWELL_EQUATION_SURFACES_STATEMENT_LOCK_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_12_POTENTIAL_FIELDSTRENGTH_BRIDGE_LOCK_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md`
- `formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean`
- `formal/python/tests/test_em_u1_micro13_maxwell_tensor_forms_compatibility_map.py`
