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
