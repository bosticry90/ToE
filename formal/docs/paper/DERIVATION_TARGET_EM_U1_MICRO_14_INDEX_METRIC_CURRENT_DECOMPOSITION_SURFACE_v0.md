# Derivation Target: EM U1 Micro-14 Index/Metric + Current Decomposition Surface v0

Spec ID:
- `DERIVATION_TARGET_EM_U1_MICRO_14_INDEX_METRIC_CURRENT_DECOMPOSITION_SURFACE_v0`

Target ID:
- `TARGET-EM-U1-MICRO-14-INDEX-METRIC-CURRENT-DECOMPOSITION-SURFACE-v0`

Classification:
- `P-POLICY`

Purpose:
- Pin statement-only index/metric raise-lower surface for `F_{μν}` and `F^{μν}` under frozen signature/index conventions.
- Pin statement-only current decomposition surface relating `J^μ` to `ρ` and `j` notation seams.
- Keep this cycle planning-only/non-claim with no derivation or theorem-promotion language.

Adjudication token:
- `EM_U1_MICRO14_INDEX_METRIC_CURRENT_ADJUDICATION: NOT_YET_DISCHARGED`

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

- Deliver one bounded index/metric + current-decomposition surface artifact that pins statement-only seams:
  - `F^{μν} := g^{μα} g^{νβ} F_{αβ}`
  - `J^0 := ρ`
  - `J^i := j^i`
- Deliver one typed harness seam in Lean for later theorem-route attachment.
- Preserve statement-only posture with no derivation or discharge claim.

## ASSUMPTION FREEZE section

- Canonical assumption classes:
  - `MATH|DEF|POLICY|SCOPE`
- Required source assumption ID:
  - `ASM-EM-U1-PHY-SOURCE-01`
- Required prerequisite convention/source tokens:
  - `EM_U1_CONVENTION_LOCK_SIGNATURE_v0: METRIC_SIGNATURE_FIXED`
  - `EM_U1_CONVENTION_LOCK_INDEX_v0: INDEX_POSITION_RULES_FIXED`
  - `EM_U1_SOURCE_OBJECT_CONVENTION_v0: CURRENT_OBJECT_DEFINED`
  - `EM_U1_SOURCE_SPLIT_CONVENTION_v0: RHO_J_SPLIT_SEAM_DEFINED`
- Required non-selection policy tokens:
  - `EM_U1_IMPORT_LANES_INTERFACE_NO_SELECTION_v0: NO_UNITS_OR_GAUGE_SELECTION`
  - `EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS`

## CANONICAL_ROUTE section

- Canonical compatibility route:
  - reference Cycle-006 signature/index lock,
  - reference Cycle-010 source/current seam lock,
  - reference Cycle-011 statement surfaces,
  - reference Cycle-012 A↔F bridge lock,
  - pin index/metric raise-lower and current decomposition seams only.
- This cycle is statement-only:
  - no implication proof is asserted,
  - no dynamics derivation is asserted,
  - no theorem discharge/promotion is asserted.

## ANTI_SHORTCUT section

- Required anti-shortcut token:
  - `EM_U1_NO_SHORTCUT_GUARD_v0: OBJECT_ROUTE_REQUIRED`
- Forbidden shortcuts:
  - elevating raise-lower or current-decomposition tags into proof/discharge claims,
  - introducing units/constitutive/gauge-fixing selections through seam wording,
  - importing derivation language into this statement-only cycle.

## COUNTERFACTUAL ROUTE section

- Counterfactual scaffold token:
  - `EM_U1_COUNTERFACTUAL_SCAFFOLD_v0: REQUIRED_ASSUMPTION_REMOVAL_BREAKS_CLOSURE`
- Without this pinned surface, index/metric and source decomposition notation can drift between artifact lanes and reopen ambiguity.

## INDEPENDENT NECESSITY ROUTE section

- Independent-necessity class token:
  - `EM_U1_INDEPENDENT_NECESSITY_CLASS_v0: OBJECT_CONSTRUCTIVE_ROUTE`
- Cycle-014 remains structural-only and does not alter theorem/discharge status.

## HARDENING section

- Cycle-014 hardening posture:
  - tokens must be synchronized across doc/Lean/target/state/roadmap,
  - explicit seam statements are localized to this cycle artifact,
  - derivation/promotion language is forbidden in this artifact.
- Hardening scaffold token:
  - `EM_U1_HARDENING_SCAFFOLD_v0: ROBUSTNESS_NEGCTRL_TEMPLATES_PINNED`

## BOUNDED_SCOPE section

- non-claim boundary is explicit and binding for this micro artifact.
- bounded index/metric + current decomposition scope only.
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

- Cycle-014 progress token:
  - `EM_U1_PROGRESS_CYCLE14_v0: INDEX_METRIC_CURRENT_DECOMPOSITION_TOKEN_PINNED`
- Index/metric seam token:
  - `EM_U1_INDEX_METRIC_RAISE_LOWER_SURFACE_v0: F_INDEX_POSITION_CONTRACT_PINNED`
- Current decomposition seam token:
  - `EM_U1_CURRENT_DECOMPOSITION_SURFACE_v0: JMU_RHOJ_SEAM_PINNED`
- Localization gate token:
  - `EM_U1_INDEX_METRIC_CURRENT_LOCALIZATION_GATE_v0: CYCLE14_ARTIFACTS_ONLY`
- No-derivation gate token:
  - `EM_U1_INDEX_METRIC_CURRENT_NO_DERIVATION_v0: STATEMENT_ONLY`

## ADJUDICATION_SYNC section

- Cycle-014 adjudication token:
  - `EM_U1_MICRO14_INDEX_METRIC_CURRENT_ADJUDICATION: NOT_YET_DISCHARGED`
- Canonical gate test pointer:
  - `formal/python/tests/test_em_u1_micro14_index_metric_current_decomposition_surface.py`

Deliverable pointers:
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_10_SOURCE_CURRENT_INTERFACE_CONTRACTS_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_11_MAXWELL_EQUATION_SURFACES_STATEMENT_LOCK_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_12_POTENTIAL_FIELDSTRENGTH_BRIDGE_LOCK_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_13_MAXWELL_TENSOR_FORMS_COMPATIBILITY_MAP_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md`
- `formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean`
- `formal/python/tests/test_em_u1_micro14_index_metric_current_decomposition_surface.py`
