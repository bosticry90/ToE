# Derivation Target: EM U1/Maxwell Object v0

Spec ID:
- `DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0`

Target ID:
- `TARGET-EM-U1-PLAN`

Classification:
- `P-POLICY`

Purpose:
- Start the EM pillar under the frozen architecture contract.
- Keep assumptions explicit and bounded while preventing scope drift.
- Define the first nontrivial EM object set and kickoff sequence under governance-enforced phase discipline.

Adjudication token:
- `EM_U1_MAXWELL_ADJUDICATION: NOT_YET_DISCHARGED`

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

- Canonical EM kickoff target remains:
  - `TARGET-EM-U1-PLAN`
- Scope is a bounded U(1)/Maxwell object lane with explicit theorem-surface dependencies.

## ASSUMPTION FREEZE section

- Canonical assumption classes are explicit:
  - `MATH|DEF|POLICY|SCOPE`
- Initial bounded assumption bundle token:
  - `EMU1Assumptions_v0`
- Required core assumptions:
  - typed gauge-potential carrier (`A_mu`) and field-strength construction (`F_munu`),
  - typed source/current carrier (`J_mu`) with continuity assumptions,
  - bounded-domain and non-radiative simplification boundaries are explicit where used.

## CANONICAL ROUTE section

- Canonical route is object-first and theorem-surface driven:
  - `A_mu` object -> `F_munu` construction -> source coupling -> bounded Maxwell-form contract.
- Canonical route must remain explicit and assumption-threaded.
- Compatibility wrappers are allowed only as non-authoritative shells.

## ANTI_SHORTCUT section

- Forbidden shortcut classes:
  - direct insertion of Maxwell equations without declared object construction chain,
  - implicit gauge-fixing assumptions not represented in the assumption bundle,
  - hidden source/current closure assumptions.
- Required anti-shortcut control token:
  - `EM_U1_NO_SHORTCUT_GUARD_v0: OBJECT_ROUTE_REQUIRED`

## COUNTERFACTUAL ROUTE section

- Counterfactual row requirements are explicit:
  - removing the gauge-contract assumptions breaks closure of the bounded theorem-surface target,
  - removing continuity assumptions breaks source-coupled closure obligations.
- Counterfactual scaffold token:
  - `EM_U1_COUNTERFACTUAL_SCaffold_v0: REQUIRED_ASSUMPTION_REMOVAL_BREAKS_CLOSURE`

## INDEPENDENT NECESSITY ROUTE section

- Structural classification requirement:
  - `EM_U1_INDEPENDENT_NECESSITY_CLASS_v0: OBJECT_CONSTRUCTIVE_ROUTE`
- Independent-necessity route must be theorem-linked and non-circular.

## HARDENING section

- Hardening must include:
  - robustness row templates,
  - negative-control row templates,
  - explicit failure-informative criteria on bounded theorem surfaces.
- Hardening scaffold token:
  - `EM_U1_HARDENING_SCAFFOLD_v0: ROBUSTNESS_NEGCTRL_TEMPLATES_PINNED`

## BOUNDED SCOPE section

- non-claim boundary is explicit and binding for this artifact.
- bounded U(1)/Maxwell object scope only.
- no non-Abelian gauge completion claim.
- no Standard Model completion claim.
- no external truth claim.

## DRIFT_GATES section

- Required drift gates:
  - architecture phase contract must remain exact,
  - assumption class set must remain explicit and bounded,
  - adjudication/token/status drift must remain lock-governed.
- Reopen trigger:
  - route mutation, hidden assumptions, or scope expansion without governance update.

## ADJUDICATION_SYNC section

- Canonical adjudication token (planning state):
  - `EM_U1_MAXWELL_ADJUDICATION: NOT_YET_DISCHARGED`
- Promotion to discharge requires synchronized update across:
  - target doc,
  - `State_of_the_Theory.md`,
  - `RESULTS_TABLE_v0.md`,
  - gate tests/artifacts.

Non-claim boundary:
- planning-only artifact.
- non-claim control surface.
- does not promote claim labels by itself.
- no comparator-lane authorization.
- no Standard Model completion claim.
- no external truth claim.

Minimum structural objects required:
- gauge field object
- field-strength object
- source/current object
- gauge-redundancy/invariance contract

Canonical EM object checklist (v0 planning):
1. Gauge potential object:
   - typed `A_mu` carrier for U(1) posture.
2. Field-strength object:
   - typed `F_munu` structure from gauge potential differentials.
3. Source/current object:
   - typed `J_mu` source carrier with explicit continuity assumptions.
4. Gauge contract:
   - explicit theorem-shaped invariance contract under U(1) gauge action.
5. Falsifiability hook:
   - explicit statement of what would invalidate this EM posture in scoped assumptions.

Cycle-001 kickoff micro-targets (now pinned):
1. `TARGET-EM-U1-MICRO-01-OBJECT-SCAFFOLD-v0`
   - scope:
     - planning-only typed-object scaffold for EM pillar activation under architecture-v1.
   - cycle token:
     - `EM_U1_PROGRESS_v0: CYCLE1_OBJECT_SCAFFOLD_TOKEN_PINNED`
   - artifact pointer:
     - `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_01_OBJECT_SCAFFOLD_v0.md`
   - lean scaffold pointer:
     - `formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean`
   - posture:
     - planning-only/non-claim and no theorem promotion authorized.

Cycle-002 kickoff micro-targets (now pinned):
1. `TARGET-EM-U1-MICRO-02-GAUGE-CONTRACT-SURFACE-v0`
   - scope:
     - planning-only gauge-contract theorem-surface scaffold under explicit assumptions.
   - cycle token:
     - `EM_U1_PROGRESS_CYCLE2_v0: GAUGE_CONTRACT_SURFACE_TOKEN_PINNED`
   - assumption-surface token:
     - `EM_U1_GAUGE_CONTRACT_ASSUMPTION_SURFACE_v0: COMMUTATIVITY_LINEARITY_PINNED`
   - derivation token:
     - `EM_U1_GAUGE_CONTRACT_DERIVATION_TOKEN_v0: FIELD_STRENGTH_INVARIANCE_FROM_DIFFERENTIAL_BUNDLE_ASSUMPTIONS`
   - artifact pointer:
     - `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_02_GAUGE_CONTRACT_SURFACE_v0.md`
   - lean scaffold pointer:
     - `formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean`
   - posture:
     - planning-only/non-claim and no theorem promotion authorized.

Cycle-003 kickoff micro-targets (now pinned):
1. `TARGET-EM-U1-MICRO-03-PREDISCHARGE-GATE-BUNDLE-v0`
   - scope:
     - planning-only pre-discharge gate bundle for EM bounded object lane.
   - cycle token:
     - `EM_U1_PROGRESS_CYCLE3_v0: PREDISCHARGE_GATE_BUNDLE_TOKEN_PINNED`
   - adjudication token:
     - `EM_U1_MICRO03_PREDISCHARGE_GATE_BUNDLE_ADJUDICATION: DISCHARGED_CONDITIONAL_v0`
   - object-route uniqueness gate token:
     - `EM_U1_OBJECT_ROUTE_ARTIFACT_UNIQUENESS_GATE_v0: SINGLE_AUTHORITATIVE_ARTIFACT_SET_REQUIRED`
   - roadmap-row uniqueness gate token:
     - `EM_U1_ROADMAP_ROW_UNIQUENESS_GATE_v0: SINGLE_ACTIVE_ROW_REQUIRED`
   - assumption-registry sync gate token:
     - `EM_U1_ASSUMPTION_REGISTRY_SYNC_GATE_v0: DIFFERENTIAL_BUNDLE_IDS_REQUIRED`
   - Maxwell-form authorization gate token:
     - `EM_U1_MAXWELL_FORM_AUTHORIZATION_GATE_v0: LOCKED_UNTIL_CYCLE3_ADJUDICATION_FLIP`
   - required assumption registry IDs:
     - `ASM-EM-U1-STR-01`
     - `ASM-EM-U1-SYM-01`
   - artifact pointer:
     - `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_03_PREDISCHARGE_GATE_BUNDLE_v0.md`
   - gate test pointer:
     - `formal/python/tests/test_em_u1_micro03_predischarge_gate_bundle.py`
   - posture:
     - planning-only/non-claim and no theorem promotion authorized.

Cycle-004 kickoff micro-targets (now pinned):
1. `TARGET-EM-U1-MICRO-04-MAXWELL-FORM-ATTEMPT-v0`
   - scope:
     - planning-only bounded Maxwell-form attempt package under explicit authorization.
   - cycle token:
     - `EM_U1_PROGRESS_CYCLE4_v0: MAXWELL_FORM_ATTEMPT_PACKAGE_TOKEN_PINNED`
   - shape gate token:
     - `EM_U1_MAXWELL_FORM_SHAPE_GATE_v0: AUTHORIZED_PRESENCE_ONLY`
   - localization gate token:
     - `EM_U1_MAXWELL_FORM_LOCALIZATION_GATE_v0: CYCLE4_ARTIFACT_ONLY`
   - cycle adjudication token:
     - `EM_U1_MICRO04_MAXWELL_FORM_ATTEMPT_ADJUDICATION: NOT_YET_DISCHARGED`
   - required authorization prerequisite:
     - `EM_U1_MICRO03_PREDISCHARGE_GATE_BUNDLE_ADJUDICATION: DISCHARGED_CONDITIONAL_v0`
   - artifact pointer:
     - `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_04_MAXWELL_FORM_ATTEMPT_PACKAGE_v0.md`
   - gate test pointer:
     - `formal/python/tests/test_em_u1_micro04_maxwell_form_attempt_shape.py`
   - posture:
     - planning-only/non-claim and no theorem promotion authorized.

Cycle-005 kickoff micro-targets (now pinned):
1. `TARGET-EM-U1-MICRO-05-MAXWELL-FORM-SEMANTICS-MAPPING-v0`
   - scope:
     - planning-only bounded semantics mapping from Maxwell-form symbols to pinned EM object carriers.
   - cycle token:
     - `EM_U1_PROGRESS_CYCLE5_v0: MAXWELL_FORM_SEMANTICS_MAPPING_TOKEN_PINNED`
   - definitional-only gate token:
     - `EM_U1_MAXWELL_SEMANTICS_DEFINITIONAL_ONLY_GATE_v0: NO_DYNAMICS_CLOSURE_CLAIM`
   - carrier mapping tokens:
     - `EM_U1_MAXWELL_SEMANTICS_MAPPING_EB_v0: E_B_FROM_FIELD_STRENGTH_CARRIER_COMPONENTS`
     - `EM_U1_MAXWELL_SEMANTICS_MAPPING_RHOJ_v0: RHO_J_FROM_CURRENT_CARRIER_COMPONENTS`
   - new-physics assumption-ID gate token:
     - `EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS`
   - cycle adjudication token:
     - `EM_U1_MICRO05_MAXWELL_FORM_SEMANTICS_MAPPING_ADJUDICATION: NOT_YET_DISCHARGED`
   - required authorization prerequisite:
     - `EM_U1_MICRO03_PREDISCHARGE_GATE_BUNDLE_ADJUDICATION: DISCHARGED_CONDITIONAL_v0`
   - artifact pointer:
     - `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_05_MAXWELL_FORM_SEMANTICS_MAPPING_v0.md`
   - gate test pointer:
     - `formal/python/tests/test_em_u1_micro05_maxwell_form_semantics_mapping.py`
   - posture:
     - planning-only/non-claim and no theorem promotion authorized.

Cycle-006 kickoff micro-targets (now pinned):
1. `TARGET-EM-U1-MICRO-06-CONVENTION-LOCK-3P1-v0`
   - scope:
     - planning-only bounded convention lock for 3+1/sign/index semantics.
   - cycle token:
     - `EM_U1_PROGRESS_CYCLE6_v0: CONVENTION_LOCK_3P1_TOKEN_PINNED`
   - convention lock tokens:
     - `EM_U1_CONVENTION_LOCK_SIGNATURE_v0: METRIC_SIGNATURE_FIXED`
     - `EM_U1_CONVENTION_LOCK_INDEX_v0: INDEX_POSITION_RULES_FIXED`
     - `EM_U1_CONVENTION_LOCK_EB_v0: E_B_SIGN_AND_EPSILON_FIXED`
     - `EM_U1_CONVENTION_LOCK_UNITS_POLICY_v0: UNITS_NOT_SELECTED`
     - `EM_U1_CONVENTION_LOCK_NO_DYNAMICS_v0: DEFINITIONAL_ONLY`
   - new-physics assumption-ID gate token:
     - `EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS`
   - cycle adjudication token:
     - `EM_U1_MICRO06_CONVENTION_LOCK_3P1_ADJUDICATION: NOT_YET_DISCHARGED`
   - required authorization prerequisite:
     - `EM_U1_MICRO03_PREDISCHARGE_GATE_BUNDLE_ADJUDICATION: DISCHARGED_CONDITIONAL_v0`
   - artifact pointer:
     - `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_06_CONVENTION_LOCK_3P1_v0.md`
   - gate test pointer:
     - `formal/python/tests/test_em_u1_micro06_convention_lock_3p1.py`
   - posture:
     - planning-only/non-claim and no theorem promotion authorized.

Cycle-007 kickoff micro-targets (now pinned):
1. `TARGET-EM-U1-MICRO-07-IMPORT-LANES-PLACEHOLDERS-v0`
   - scope:
     - planning-only bounded import-lane placeholder control for constitutive/units/gauge-fixing surfaces.
   - cycle token:
     - `EM_U1_PROGRESS_CYCLE7_v0: IMPORT_LANES_PLACEHOLDERS_TOKEN_PINNED`
   - localization gate token:
     - `EM_U1_IMPORT_LANES_LOCALIZATION_GATE_v0: CONSTITUTIVE_UNITS_GFIXING_ONLY_IN_CYCLE7_ARTIFACTS`
   - placeholder-only gate token:
     - `EM_U1_IMPORT_LANES_NO_DYNAMICS_v0: PLACEHOLDER_ONLY`
   - new-physics assumption-ID gate token:
     - `EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS`
   - required import-lane assumption IDs:
     - `ASM-EM-U1-PHY-CONSTITUTIVE-01`
     - `ASM-EM-U1-PHY-UNITS-01`
     - `ASM-EM-U1-PHY-GFIX-01`
   - cycle adjudication token:
     - `EM_U1_MICRO07_IMPORT_LANES_ADJUDICATION: NOT_YET_DISCHARGED`
   - artifact pointer:
     - `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_07_IMPORT_LANES_PLACEHOLDERS_v0.md`
   - gate test pointer:
     - `formal/python/tests/test_em_u1_micro07_import_lanes_placeholders.py`
   - posture:
     - planning-only/non-claim and no theorem promotion authorized.

Cycle-008 kickoff micro-targets (now pinned):
1. `TARGET-EM-U1-MICRO-08-IMPORT-LANES-INTERFACE-CONTRACTS-v0`
   - scope:
     - planning-only bounded import-lane interface-contract seams for constitutive/units/gauge-fixing attachments.
   - cycle token:
     - `EM_U1_PROGRESS_CYCLE8_v0: IMPORT_LANES_INTERFACE_CONTRACTS_TOKEN_PINNED`
   - interface-contract token:
     - `EM_U1_IMPORT_LANES_INTERFACE_CONTRACTS_v0: THREE_LANE_INTERFACES_DEFINED`
   - no-selection token:
     - `EM_U1_IMPORT_LANES_INTERFACE_NO_SELECTION_v0: NO_UNITS_OR_GAUGE_SELECTION`
   - localization gate token:
     - `EM_U1_IMPORT_LANES_INTERFACE_LOCALIZATION_GATE_v0: CYCLE7_CYCLE8_ARTIFACTS_ONLY`
   - interface-application harness token:
     - `EM_U1_IMPORT_LANES_INTERFACE_APPLICATION_HARNESS_v0: REFERENCE_ONLY_IMPORT_APPLICATION`
   - no-dynamics token:
     - `EM_U1_IMPORT_LANES_NO_DYNAMICS_v0: PLACEHOLDER_ONLY`
   - required import-lane assumption IDs:
     - `ASM-EM-U1-PHY-CONSTITUTIVE-01`
     - `ASM-EM-U1-PHY-UNITS-01`
     - `ASM-EM-U1-PHY-GFIX-01`
   - cycle adjudication token:
     - `EM_U1_MICRO08_IMPORT_LANES_INTERFACE_ADJUDICATION: NOT_YET_DISCHARGED`
   - artifact pointer:
     - `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_08_IMPORT_LANES_INTERFACE_CONTRACTS_v0.md`
   - gate test pointer:
     - `formal/python/tests/test_em_u1_micro08_import_lanes_interface_contracts.py`
   - posture:
     - planning-only/non-claim and no theorem promotion authorized.

Cycle-009 kickoff micro-targets (now pinned):
1. `TARGET-EM-U1-MICRO-09-DUAL-HODGE-CONVENTION-LOCK-v0`
   - scope:
     - planning-only bounded 4D dual/epsilon/Hodge convention-lock scaffold with no dynamics claims.
   - cycle token:
     - `EM_U1_PROGRESS_CYCLE9_v0: DUAL_HODGE_CONVENTION_LOCK_TOKEN_PINNED`
   - dual-convention token:
     - `EM_U1_DUAL_CONVENTION_v0: STARF_DEFINITION_FIXED`
   - epsilon-convention token:
     - `EM_U1_EPSILON_CONVENTION_v0: LEVI_CIVITA_NORMALIZATION_FIXED`
   - hodge-star convention token:
     - `EM_U1_HODGE_STAR_CONVENTION_v0: STARSTAR_SIGN_FIXED_UNDER_SIGNATURE`
   - localization gate token:
     - `EM_U1_DUAL_HODGE_LOCALIZATION_GATE_v0: CYCLE6_CYCLE9_ARTIFACTS_ONLY`
   - no-dynamics token:
     - `EM_U1_DUAL_HODGE_NO_DYNAMICS_v0: CONVENTION_LOCK_ONLY`
   - required convention prerequisite tokens:
     - `EM_U1_CONVENTION_LOCK_SIGNATURE_v0: METRIC_SIGNATURE_FIXED`
     - `EM_U1_CONVENTION_LOCK_EB_v0: E_B_SIGN_AND_EPSILON_FIXED`
   - cycle adjudication token:
     - `EM_U1_MICRO09_DUAL_HODGE_ADJUDICATION: NOT_YET_DISCHARGED`
   - artifact pointer:
     - `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_09_DUAL_HODGE_CONVENTION_LOCK_v0.md`
   - gate test pointer:
     - `formal/python/tests/test_em_u1_micro09_dual_hodge_convention_lock.py`
   - posture:
     - planning-only/non-claim and no theorem promotion authorized.

Cycle-010 kickoff micro-targets (now pinned):
1. `TARGET-EM-U1-MICRO-10-SOURCE-CURRENT-INTERFACE-CONTRACTS-v0`
   - scope:
     - planning-only bounded source/current interface seams with optional continuity predicate contract only.
   - cycle token:
     - `EM_U1_PROGRESS_CYCLE10_v0: SOURCE_CURRENT_INTERFACE_TOKEN_PINNED`
   - source-object convention token:
     - `EM_U1_SOURCE_OBJECT_CONVENTION_v0: CURRENT_OBJECT_DEFINED`
   - source-split convention token:
     - `EM_U1_SOURCE_SPLIT_CONVENTION_v0: RHO_J_SPLIT_SEAM_DEFINED`
   - continuity predicate token:
     - `EM_U1_SOURCE_CONTINUITY_PREDICATE_v0: OPTIONAL_INTERFACE_CONSTRAINT_ONLY`
   - localization gate token:
     - `EM_U1_SOURCE_LOCALIZATION_GATE_v0: CYCLE10_ARTIFACTS_ONLY`
   - no-dynamics token:
     - `EM_U1_SOURCE_NO_DYNAMICS_v0: INTERFACE_ONLY`
   - required source assumption ID:
     - `ASM-EM-U1-PHY-SOURCE-01`
   - cycle adjudication token:
     - `EM_U1_MICRO10_SOURCE_CURRENT_ADJUDICATION: NOT_YET_DISCHARGED`
   - artifact pointer:
     - `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_10_SOURCE_CURRENT_INTERFACE_CONTRACTS_v0.md`
   - gate test pointer:
     - `formal/python/tests/test_em_u1_micro10_source_current_interface_contracts.py`
   - posture:
     - planning-only/non-claim and no theorem promotion authorized.

Unlock condition:
- `LOCKED` until `TARGET-GR01-DERIV-CHECKLIST-PLAN` is `CLOSED` in `PHYSICS_ROADMAP_v0.md`.

Closure definition:
- typed EM theorem/derivation surface exists with explicit assumptions.
- domain-of-validity and falsifiability hooks are explicit.
- paper/state/results pointers are synchronized.

Non-claim boundary reinforcement:
- no non-Abelian gauge completion claim.
- no Standard Model completion claim.
- no external truth claim.
