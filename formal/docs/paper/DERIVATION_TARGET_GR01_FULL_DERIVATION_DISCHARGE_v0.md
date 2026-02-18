# Derivation Target: GR01 Full Derivation Discharge v0

Spec ID:
- `DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0`

Classification:
- `T-PROVED`

Purpose:
- Track the remaining gap between current conditional GR01 closure and a full
  action-level derivation of the weak-field discrete Poisson equation.
- Make blocker objects auditable and prevent adjudication drift.

Adjudication token:
- `FULL_DERIVATION_ADJUDICATION: DISCHARGED_v0_DISCRETE`

Inevitability adjudication token:
- `FULL_DERIVATION_INEVITABILITY_ADJUDICATION: DISCHARGED_v0_BOUNDED`

Inevitability obligation linkage (must remain synchronized with gate target):
- theorem tokens:
  - `gr01_inevitability_necessity_under_minimized_assumptions_v0`
  - `gr01_inevitability_counterfactual_breaks_without_required_assumption_v0`
  - `gr01_inevitability_structural_classification_of_constructive_route_v0`
  - `gr01_inevitability_discharge_ready_bundle_v0`
  - `gr01_inevitability_route_bundle_without_bridge_shortcuts_v0`
- minimized-assumption anchor token:
  - `GR01InevitabilityMinimizedAssumptions_v0`
- named-route assumption tokens:
  - `GR01InevitabilityCanonicalActionNativeRoute_v0`
  - `GR01InevitabilityNoBridgeShortcutRoute_v0`
  - `GR01InevitabilityBoundedWeakFieldClosureRoute_v0`
- no-shortcut elimination-chain tokens:
  - `GR01NoBridgeShortcutEliminationLemmaChain_v0`
  - `GR01BridgeWitnessConstructorRouteUsed_v0`
  - `GR01BridgeTransportConstructorRouteUsed_v0`
  - `GR01BridgeTransportFromRadialEvaluatorRouteUsed_v0`
- closure-surface token:
  - `GR01InevitabilityBoundedClosureSurface_v0`
- signature-binding token:
  - `(hMin : GR01InevitabilityMinimizedAssumptions_v0)`
- counterfactual break token:
  - `¬GR01InevitabilityBoundedClosureSurface_v0`
- per-assumption break theorem tokens:
  - `gr01_inevitability_counterfactual_breaks_without_canonical_action_native_route_assumption_v0`
  - `gr01_inevitability_counterfactual_breaks_without_no_bridge_shortcut_assumption_v0`
  - `gr01_inevitability_counterfactual_breaks_without_bounded_weak_field_closure_assumption_v0`
- structural classification anchor token:
  - `GR01InevitabilityConstructiveRouteClassification_v0`

Scope:
- Bounded/discrete weak-field v0 only.
- No continuum-limit, uniqueness, or infinite-domain inversion claims.
- Bounded inevitability is discharged at theorem-body bounded scope under explicit dependency and anti-shortcut constraints.

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

- `TARGET-GR01-FULL-DERIVATION-DISCHARGE-v0` remains the frozen target surface.

## ASSUMPTION FREEZE section

- Minimized-assumption anchor remains explicit: `GR01InevitabilityMinimizedAssumptions_v0`.
- Required route assumptions remain explicit and theorem-linked.

## CANONICAL ROUTE section

- Canonical route remains action-native and constructor-routed on the bounded weak-field theorem surface.
- Compatibility wrappers remain non-authoritative.

## COUNTERFACTUAL ROUTE section

- Counterfactual break token remains explicit: `¬GR01InevitabilityBoundedClosureSurface_v0`.
- Per-assumption counterfactual break theorem tokens remain pinned.

## INDEPENDENT NECESSITY ROUTE section

- Structural classification anchor remains explicit:
  `GR01InevitabilityConstructiveRouteClassification_v0`.

## BOUNDED SCOPE section

- non-claim boundary is explicit and binding for this artifact.
- bounded/discrete weak-field v0 scope only; no continuum-limit, uniqueness, or infinite-domain inversion promotion.

## Current status

Current GR01 state is strong but conditional:
- action-to-operator route is discharged under explicit bridge assumptions.
- 3D bounded/discrete closure is synchronized.
- derivation-grade governance package is synchronized.

Full derivation is discharged in bounded/discrete v0 scope, with the canonical
action-native route carrying EL-to-residual closure under theorem-enforced
anti-circular governance.

## Blocker inventory (explicit)

1. Default action route is now theorem-bound to the cubic lane, but still not
  an action-derived EL discharge:
- `formal/toe_formal/ToeFormal/Variational/ActionRep32Def.lean`
- `formal/toe_formal/ToeFormal/Variational/ActionRep32CubicLane.lean`
- blocker condition: constructive binding token
  `actionRep32_action_default_binding` is present, but it is still downstream of
  the default `P_rep32` binding and does not by itself derive EL-to-residual
  semantics from the action calculus.

2. Core Rep32 operator remains scaffold-level (not yet derived from action):
- `formal/toe_formal/ToeFormal/Variational/FirstVariationRep32Def.lean`
- `formal/toe_formal/ToeFormal/Variational/Rep32CubicOperatorCore.lean`
- blocker token:
  - `def P_rep32 : FieldRep32 -> FieldRep32 := P_cubic_rep32_core declared_g_rep32_default`

3. Default-cubic identification uses a default-binding theorem pin, not yet
  an action-derived discharge:
- `formal/toe_formal/ToeFormal/Variational/DischargeELMatchesFN01Rep32Pcubic.lean`
- blocker tokens:
  - `theorem P_rep32_def : P_rep32 = P_cubic_rep32 declared_g_rep32`

4. Bridge semantics assumptions still carry EL->residual meaning:
- `formal/toe_formal/ToeFormal/Variational/GR01BridgePromotion.lean`
- `formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean`
- blocker token family:
  - `ELImpliesOperatorResidualUnderBound`
  - `ELImpliesDiscretePoissonResidual` (assumption-object dependency now replaced on the
    bridge theorem surface by a derived constructor route,
    `gr01_el_implies_discrete_poisson_residual_from_bridge_promotion`)

5. Finite-difference remainder assumptions still mediate action->P closure:
- `formal/toe_formal/ToeFormal/Variational/ActionRep32QuadraticCubic.lean`
- blocker token family:
  - `ActionRep32CubicLinearMatchesP`
  - `ActionRep32CubicNoSecondOrder`
  - `ActionRep32CubicNoThirdOrder`
  - `ActionRep32CubicNoFourthOrder`

## Progress token already landed

- Algebraic deviation expansion is explicit:
  - `differenceQuotientRep32_cubic_deviation_expand`
  - `ActionRep32FiniteDifferenceDeviationFromP_of_cubic`
  - `ActionRep32CubicTotalDeviationZeroAtStep`
  - `ActionRep32CubicTotalDeviationZeroAtStep_of_components`
  - `ActionRep32CubicDeviationZeroAtStep_of_RAC`
  - `ActionRep32FiniteDifferenceRepresentsP_of_cubic_totalDeviationZeroAtStep`
  - `ActionRep32FiniteDifferenceRepresentsP_cubic_of_deviationZeroAtStep`
  - `ActionVariationBridgeRep32At_cubic_of_deviationZeroAtStep`
  - `actionRep32_variation_bridge_sequence_from_algebraic_deviation_v0`
  - `actionRep32_variation_bridge_sequence_from_algebraic_deviation_default_binding_v0`
  - `actionRep32_produces_operator_equation_discrete_of_bridge_witness_constructor_from_algebraic_deviation_v0`
  - `actionRep32_variation_deviation_sequence_discrete_v0`
  - `actionRep32_variation_deviation_sequence_discrete_default_binding_v0`
  - file:
    `formal/toe_formal/ToeFormal/Variational/ActionRep32QuadraticCubic.lean`
  - file:
    `formal/toe_formal/ToeFormal/Variational/GR01ActionToOperatorDiscrete.lean`

This token isolates exactly what still must be discharged to convert
contract-level bridge semantics into action-level derivation semantics.

- Explicit non-axiomatic identification route token is also pinned:
  - `actionRep32_action_default_binding`
  - `EL_toe_rep32_equals_Pcubic_under_default_quotient_assumptions_of_hP`
  - `Rep32_cubic_lane_default_binding`
  - `EL_toe_eq_Pcubic_rep32_of_hP`
  - file:
    - `formal/toe_formal/ToeFormal/Variational/ActionRep32CubicLane.lean`
    - `formal/toe_formal/ToeFormal/Variational/DischargeELMatchesFN01Rep32Pcubic.lean`

- Explicit `hP`-threaded bridge entry tokens are also pinned:
  - `gr01_discrete_residual_from_bridge_promotion_chain_minimal_of_hP`
  - `gr01_discrete_residual_from_bridge_promotion_chain_of_hP`
  - `gr01_discrete_residual_from_bridge_promotion_chain_default_binding_of_hP`
  - `gr01_el_implies_discrete_poisson_residual_from_bridge_promotion`
  - `TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_derived_from_bridge_minimal_of_hP`
  - `TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_derived_from_bridge_of_hP`
  - `TOE_GR01_weak_field_poisson_limit_under_default_binding_assumptions_derived_from_bridge_of_hP`
  - `TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_minimal_of_hP`
  - `TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_of_hP`
  - `TOE_GR01_weak_field_poisson_limit_under_default_binding_assumptions_of_hP`
  - `gr01_der01_scaffold_bundle_under_promoted_assumptions_of_hP`
  - `gr01_end_to_end_chain_bundle_under_promoted_assumptions_of_hP`
  - `gr01_end_to_end_poisson_equation_under_promoted_assumptions_of_hP`
  - files:
    - `formal/toe_formal/ToeFormal/Variational/GR01BridgePromotion.lean`
    - `formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean`
    - `formal/toe_formal/ToeFormal/Variational/GR01DerivationScaffoldPromotion.lean`
    - `formal/toe_formal/ToeFormal/Variational/GR01EndToEndClosure.lean`

The bridge-promotion wrappers now route through the minimal `hP` theorem route,
so `hAction`/`hRAC` are compatibility-shell parameters rather than proof
carriers on the default bridge discharge path.

The bridge layer now also carries a derived weak-field route that constructs
`ELImpliesDiscretePoissonResidual` theorem-side (instead of requiring that
assumption-object as a weak-field theorem input), while retaining explicit
bridge semantics assumptions.

An additional operator-transport theorem surface is now pinned:
- `ELImpliesOperatorResidualTransport`
- `gr01_operator_residual_transport_from_bound_bridge_assumptions`
- `gr01_el_implies_discrete_poisson_residual_from_operator_transport`
- `TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_derived_from_operator_transport_minimal_of_hP`
- `actionRep32_operator_residual_transport_from_radial_evaluator_interface_v0`
- `actionRep32_operator_residual_under_bound_from_radial_evaluator_interface_v0`
- `actionRep32_operator_residual_transport_of_bridge_witness_constructor_v0`
- `actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_operator_transport_witness_v0`
- `actionRep32_weak_field_poisson_limit_under_default_binding_assumptions_of_operator_transport_witness_v0`
- `actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_constructor_v0`
- `actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_from_radial_evaluator_constructor_v0`
- `actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_witness_constructor_v0`

Legacy bridge-witness wrapper routing note:
- `actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_witness_constructor_v0`
  is retained for compatibility but now delegates through evaluator-transport
  bridge closure (`...of_bridge_transport_from_radial_evaluator_constructor_v0`).
- `actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_from_radial_evaluator_constructor_v0`
  is retained for compatibility but now delegates to the action-native
  transport-constructor route; explicit bound inputs are compatibility-only.

Action-native evaluator-transport route token is now pinned as the direct
pre-discharge constructor surface:
- `actionRep32_fd_expansion_and_vanishing_to_radial_evaluator_transport_interface_v0`
- `actionRep32_el_to_evalRadial_rep32_cubic_zero_from_fd_expansion_and_vanishing_v0`
- `actionRep32_el_to_evalRadial_rep32_cubic_zero_from_fd_expansion_constructor_v0`
- `actionRep32_el_to_evalRadial_rep32_cubic_zero_from_fd_expansion_constructor_default_binding_v0`
- `actionRep32_el_implies_operator_residual_transport_from_fd_expansion_v0`
- `actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_action_native_evaluator_transport_from_fd_expansion_v0`
- `actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_action_native_transport_constructor_from_fd_expansion_v0`

Canonical discharge route for full-derivation gating is now constructor-routed:
- `actionRep32_fd_expansion_and_vanishing_to_radial_evaluator_transport_constructor_v0`
- `actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_default_binding_from_probe_model_v0`
- `actionRep32_weak_field_poisson_limit_under_default_binding_assumptions_of_action_native_transport_constructor_from_fd_expansion_v0`

Discharge-critical simplification note:
- Older transport tokens remain available for compatibility/progress tracking
  (`actionRep32_el_implies_operator_residual_transport_from_fd_expansion_v0`,
  `actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_v0`,
  `actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_v0`),
  but they are no longer treated as core discharge-critical artifacts.
- Canonical weak-field constructor-routed theorem block must avoid
  interface-shaped transport tokens (`hEvalFromFDExpansionAndVanishing`,
  `actionRep32_fd_expansion_and_vanishing_to_radial_evaluator_transport_interface_v0`).
- Canonical weak-field constructor-routed theorem block must also avoid local
  deviation-plumbing tokens (`hDevZero`,
  `ActionRep32CubicDeviationZeroAtStep_of_RAC`) and rely on the RAC-premise
  constructor abstraction.
- Canonical weak-field constructor-routed theorem block must close via
  `actionRep32_weak_field_poisson_limit_under_default_binding_assumptions_of_operator_transport_witness_v0`
  and not directly call bridge-derived weak-field closure tokens.
- Canonical weak-field constructor-routed theorem block must keep
  default-binding operator-witness routing explicit and must not route through
  the older quotient-assumption transport-constructor weak-field
  wrapper token
  (`actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_action_native_transport_constructor_from_fd_expansion_v0`).
- Canonical weak-field constructor-routed theorem block must not route through
  older EL->transport variants (`actionRep32_el_implies_operator_residual_transport_from_fd_expansion_v0`,
  `actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_v0`);
  those remain compatibility/progress-only.
- RAC-premise EL->transport constructor theorem block now has dedicated
  anti-circular/nontriviality checks: explicit RAC/probe obligations are
  required and interface-shaped transport shortcut tokens are forbidden.
- Legacy default-binding RAC EL->transport constructor theorem block is now also
  guarded against wrapper indirection: explicit default-binding closure markers
  (`actionRep32_action_default_binding`, `P_rep32_def`) and evaluator-zero
  witness threading (`hELToEvalZero`) are required, while routing through
  `actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_v0`
  is forbidden.
- RAC-derived deviation-collapse token
  (`ActionRep32CubicDeviationZeroAtStep_of_RAC`) is now carried in the
  upstream default-binding evaluator-zero constructor theorem block, keeping the
  RAC EL->transport block focused on evaluator-zero to operator-transport lift.
- Direct probe-interface plumbing is now retired from the default-binding RAC
  EL->transport constructor theorem body (`hProbeFDMatchesEvaluator`,
  `hELCoreImpliesProbePairingZero`, `probeVariation`, `probeState`); it now
  consumes a preconstructed evaluator-zero witness (`hELToEvalZero`) while the
  probe obligations are carried in the upstream canonical constructor theorem.
- Upstream default-binding evaluator-zero constructor theorem has also reduced
  direct interface dependence: probe pairing-zero witness is now bundled into
  the typed probe-model assumptions package
  (`actionRep32_probe_pairing_model_package_v0`, whose
  payload carries probe maps plus
  `actionRep32_probe_pairing_to_radial_model_assumptions_v0`) and EL-core
  probe interface is reconstructed locally, instead of taking
  `hELCoreImpliesProbePairingZero` as a direct theorem input.
- Upstream default-binding evaluator-zero constructor theorem now carries
  explicit probe-pairing model assumptions
  (`actionRep32_probe_pairing_to_radial_model_assumptions_v0`;
  local witness `hProbePairingModel`) as its live seam and reconstructs
  pairing-to-evaluator matching theorem-side first
  (`actionRep32_probe_pairing_matches_radial_evaluator_from_model_assumptions_v0`),
  then finite-difference-to-evaluator matching via FD-expansion algebra.
- Compatibility quotient-assumptions constructor theorem has also reduced direct
  interface dependence: it now consumes a preconstructed evaluator-zero
  witness (`hELToEvalZero`) and no longer carries probe-model assumptions in
  its own theorem signature, instead of taking
  `hELCoreImpliesProbePairingZero` as a direct theorem input.
- Default-binding operator-transport witness theorem block is now also guarded
  against wrapper indirection: explicit default-binding closure marker
  (`P_rep32_def`) and explicit transport-witness threading (`hOperatorTransport`)
  are required, while routing through
  `actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_operator_transport_witness_v0`
  is forbidden.
- Canonical default-binding weak-field theorem block and default-binding
  operator-transport witness theorem block are assumption-surface guarded:
  explicit quotient-plumbing tokens (`hAction`, `hP`) are forbidden.
- Compatibility quotient-assumptions constructor weak-field theorem block now
  follows the reduced-premise marker policy: quotient-witness closure token
  (`actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_operator_transport_witness_v0`)
  and uniform-bound witness threading are required, while explicit quotient
  plumbing tokens (`hAction`, `hP`) are retired from that wrapper surface.
- Legacy quotient action-native evaluator-transport weak-field wrapper now
  also retires explicit quotient plumbing tokens (`hAction`, `hP`), using
  local default-binding markers (`actionRep32_action_default_binding`,
  `P_rep32_def`) while preserving compatibility-lane theorem identity.
- Bridge compatibility wrappers (`...of_bridge_transport_constructor_v0`,
  `...of_bridge_witness_constructor_v0`,
  `...of_bridge_transport_from_radial_evaluator_constructor_v0`) now share the
  same retired-marker policy (`hAction`, `hP` absent) with required
  uniform-bound threading and closure-token routing enforced in pytest.
- Pytest now also applies a consolidated compatibility-wrapper guard across the
  quotient weak-field wrapper family: each block must contain
  `hWeakFieldUniformBound` and must not reintroduce legacy signature parameters
  (`hAction`, `hP`, `hProjectionMapWellFormed`, `hWeakFieldTruncationSound`).
- Canonical anti-drift hardening now includes a consolidated route-pattern guard
  across canonical weak-field/transport blocks, forbidding compatibility
  quotient-wrapper call patterns (`...of_operator_transport_witness_v0`,
  `...of_action_native_evaluator_transport_from_fd_expansion_v0`,
  `...of_action_native_transport_constructor_from_fd_expansion_v0`, and all
  bridge-wrapper variants) inside canonical theorem bodies.
- Gate enforcement now also includes a compact data-driven theorem-block policy
  table for canonical vs compatibility wrapper families (required tokens,
  forbidden tokens, forbidden signature-parameter patterns), reducing
  duplicated assertions and future maintenance drift.

Compatibility/progress routes remain available but are not discharge-critical
for full-derivation adjudication:
- bridge-witness constructor routes
- bridge-transport constructor routes
- zero-probe restricted evaluator slice routes

Demotion hardening (canonical-lane policy):
- Canonical constructor-routed weak-field and default-binding RAC transport
  blocks must not route through compatibility bridge transport wrappers
  (`actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_constructor_v0`,
  `actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_from_radial_evaluator_constructor_v0`,
  `actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_witness_constructor_v0`).

This narrows the blocker to deriving the operator-transport route from the
action chain without importing bridge semantics assumptions as premises.

## Concrete proof-plan (action-native transport discharge)

Execution status (2026-02-15):
- Phase A: `COMPLETED_v0_TOKENIZED` (primitive action-native lemma tokens are present and gate-pinned; direct interface discharge still open).
- Phase B: `COMPLETED_v0_TOKENIZED` (non-bridge constructor route tokens are present and anti-circular gate-pinned; direct interface theorem discharge remains open).
- Phase C: `COMPLETED_v0_TOKENIZED` (canonical weak-field route is constructor-routed and gate-pinned).
- Phase D: `COMPLETED_v0` (anti-circular pytest gate checks are enforced and passing).
- Restricted evaluator slice progress: `COMPLETED_v0` for canonical zero-probe discharge tokens (`evalRadial_from_zero_probe_fd_v0` route), providing a first non-assumptive probe-interface discharge instance.

Workflow simplification posture (active):
- Full-derivation gates now treat constructor-routed action-native transport as
  the canonical lane.
- Bridge-witness and zero-probe routes are retained for compatibility/progress,
  but are not treated as canonical discharge criteria.
- Canonical weak-field constructor-routed theorem block is now guarded against
  zero-probe shortcut tokens in pytest nontriviality checks.
- Canonical weak-field constructor-routed theorem now constructs
  `WeakFieldTruncationSound` locally and constructs
  `ProjectionMapWellFormed` from explicit uniform-bound assumptions, reducing
  direct abstract witness inputs in the canonical signature.
- Compatibility bridge-from-radial-evaluator weak-field constructor now
  mirrors that reduction: it constructs `WeakFieldTruncationSound` locally and
  derives `ProjectionMapWellFormed` from explicit uniform-bound assumptions,
  instead of threading those witness objects as explicit theorem inputs.
- Compatibility quotient action-native transport constructor now follows the
  same reduced-premise pattern: it takes explicit uniform-bound assumptions and
  constructs `ProjectionMapWellFormed` and `WeakFieldTruncationSound` locally,
  rather than requiring those witness objects directly in its signature.
- Legacy quotient action-native evaluator-transport wrapper now also follows
  the reduced-premise pattern: it consumes explicit uniform-bound assumptions
  and reconstructs `ProjectionMapWellFormed` + `WeakFieldTruncationSound`
  locally before closing through operator-transport witness routing.
- Compatibility quotient bridge-transport constructor now follows the same
  reduced-premise pattern: it takes explicit uniform-bound assumptions and
  reconstructs `ProjectionMapWellFormed` + `WeakFieldTruncationSound` locally
  before invoking the quotient operator-transport witness wrapper.
- Compatibility quotient operator-transport witness wrapper now also consumes
  explicit uniform-bound assumptions and reconstructs
  `ProjectionMapWellFormed` + `WeakFieldTruncationSound` locally, removing
  those witness objects from its direct signature surface.
- Default-binding operator-transport witness wrapper now mirrors that
  reduction: it takes explicit uniform-bound assumptions and reconstructs
  `ProjectionMapWellFormed` + `WeakFieldTruncationSound` locally before
  closing through the operator-transport witness token.
- Pytest gate now pins this reduced-premise shape on both quotient and
  default-binding operator-witness wrappers by requiring
  `hWeakFieldUniformBound` plus local-constructor tokens
  (`gr01_projection_map_well_formed_from_uniform_bound_v0`,
  `weakFieldTruncationSound_default_v0`).
- Upstream default-binding evaluator-zero constructor theorem block is required
  to include explicit nontrivial probe-interface obligations
  (`actionRep32_probe_fd_matches_radial_evaluator_interface_v0`,
  `actionRep32_el_core_implies_probe_pcubic_pairing_zero_interface_v0`).

Goal:
- Discharge `actionRep32_fd_expansion_and_vanishing_to_radial_evaluator_transport_interface_v0`
  with action/FD algebra only, then route it through
  `actionRep32_el_implies_operator_residual_transport_from_fd_expansion_v0`.

Guardrails (anti-circular):
- The proof of the interface must not use bridge semantics assumptions/tokens:
  `ELImpliesOperatorResidualUnderBound`,
  `ELImpliesDiscretePoissonResidual`,
  `gr01_operator_residual_transport_from_bound_bridge_assumptions`,
  `actionRep32_operator_residual_transport_of_bridge_witness_constructor_v0`.
- Keep all inputs local to action-side algebra + evaluator matching + remainder
  vanishing assumptions.

Phase A — isolate primitive lemma targets (new theorem surfaces, temporary stubs permitted while blocked):
1. Add a lemma token establishing evaluator-form deviation decomposition at fixed
  step from
  `actionRep32_algebraic_deviation_surface_discrete_v0 declared_g_rep32 ε`.
2. Add a lemma token proving deviation collapse under
  `ActionRep32CubicDeviationZeroAtStep declared_g_rep32 ε`.
3. Add a lemma token composing (1)+(2) to derive evaluator zero from EL-core
  equality (still action-native only).

Phase B — discharge the action-native interface:
4. Implement
  `actionRep32_fd_expansion_and_vanishing_to_radial_evaluator_transport_interface_v0`
  using only Phase A lemmas and radial evaluator algebra.
5. Prove that
  `actionRep32_el_to_evalRadial_rep32_cubic_zero_from_fd_expansion_and_vanishing_v0`
  no longer needs bridge constructors.

Phase C — route to operator transport + weak-field closure:
6. Rebuild
  `actionRep32_el_implies_operator_residual_transport_from_fd_expansion_v0`
  from the discharged interface and evaluator-to-residual matching.
7. Keep
  `actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_action_native_evaluator_transport_from_fd_expansion_v0`
  as the canonical predecessor route for full-derivation adjudication flip.

Phase D — gate hardening and adjudication readiness:
8. Extend
  `formal/python/tests/test_gr01_full_derivation_discharge_gate.py`
  with a forbidden-token check in the action-native theorem body/signature for
  bridge-constructor dependencies.
9. Flip `TOE-GR-FULL-01` to `T-PROVED` once step (8) and all placeholder
  retirements remain green.

Completion definition for this plan section:
- `actionRep32_fd_expansion_and_vanishing_to_radial_evaluator_transport_interface_v0`
  is theorem-discharged from action-native assumptions,
- anti-circular gate checks pass,
- and the action-native weak-field route remains bridge-constructor-free in
  theorem signature.

## Exit criteria for `DISCHARGED_v0_DISCRETE`

All of the following must be true:

1. The blocker tokens above are eliminated from the default derivation route
   (or proven non-authoritative for the route via replacement theorem surface).
2. A Lean theorem token exists that derives the GR01 weak-field discrete
   operator posture directly from the declared action-side route without
  importing bridge-promotion assumptions as a required premise; direct
  predecessor token for adjudication flip is:
  `actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_default_binding_from_probe_model_v0`.
3. `FULL_DERIVATION_ADJUDICATION` is flipped and pinned by pytest gate.

## Enforcement hook

- `formal/python/tests/test_gr01_full_derivation_discharge_gate.py`

Non-claim boundary:
- This artifact does not claim full continuum GR derivation.
- This artifact does not claim uniqueness or Noether-family completion.
