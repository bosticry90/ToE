# Derivation Target: QM Full Derivation Discharge v0

Spec ID:
- `DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0`

Target ID:
- `TARGET-QM-FULL-DERIVATION-DISCHARGE-v0`

Classification:
- `P-POLICY`

Purpose:
- Define an authoritative route from contract-level QM evolution (`TOE-QM-THM-01`)
  toward a derivation-grade QM evolution closure package.

Adjudication token:
- `QM_FULL_DERIVATION_ADJUDICATION: DISCHARGED_v0_DERIVATION_GRADE`

Inevitability adjudication token:
- `QM_FULL_DERIVATION_INEVITABILITY_ADJUDICATION: DISCHARGED_v0_BOUNDED`

Inevitability obligation linkage (must remain synchronized with gate target):
- theorem tokens:
  - `qm_inevitability_necessity_under_minimized_assumptions_v0`
  - `qm_inevitability_counterfactual_breaks_without_required_assumption_v0`
  - `qm_inevitability_structural_classification_of_constructive_route_v0`
  - `qm_inevitability_discharge_ready_bundle_v0`
  - `qm_inevitability_route_bundle_without_shortcuts_v0`
- minimized-assumption anchor token:
  - `QMInevitabilityMinimizedAssumptions_v0`
- named-route assumption tokens:
  - `QMInevitabilityCanonicalConstructiveRoute_v0`
  - `QMInevitabilityUnitaryConsistencyRoute_v0`
  - `QMInevitabilityNoDirectSchrodingerInsertionRoute_v0`
- no-shortcut elimination-chain tokens:
  - `QMNoDirectInsertionEliminationLemmaChain_v0`
  - `QMDirectSchrodingerInsertionRouteUsed_v0`
  - `QMContractBridgeCompatibilityWrapperRouteUsed_v0`
- closure-surface token:
  - `QMInevitabilityClosureSurface_v0`
- signature-binding token:
  - `(hMin : QMInevitabilityMinimizedAssumptions_v0 h)`
- counterfactual break token:
  - `¬QMInevitabilityClosureSurface_v0`
- per-assumption break theorem tokens:
  - `qm_inevitability_counterfactual_breaks_without_canonical_constructive_route_assumption_v0`
  - `qm_inevitability_counterfactual_breaks_without_unitary_consistency_assumption_v0`
  - `qm_inevitability_counterfactual_breaks_without_no_direct_schrodinger_insertion_assumption_v0`
- structural classification anchor token:
  - `QMInevitabilityConstructiveRouteClassification_v0`

Progress token:
- `QM_FULL_DERIVATION_PROGRESS_v0: CYCLE1_CONTRACT_BRIDGE_TOKEN_PINNED`
- `QM_FULL_DERIVATION_PROGRESS_CYCLE2_v0: UNITARY_CONSISTENCY_TOKEN_PINNED`
- `QM_FULL_DERIVATION_PROGRESS_CYCLE3_v0: ANTI_CIRCULARITY_GUARD_TOKEN_PINNED`
- `QM_FULL_DERIVATION_PROGRESS_CYCLE4_v0: COMPOSITION_BUNDLE_TOKEN_PINNED`
- `QM_FULL_DERIVATION_PROGRESS_CYCLE5_v0: ASSUMPTION_MINIMIZATION_TOKEN_PINNED`
- `QM_FULL_DERIVATION_PROGRESS_CYCLE6_v0: EXIT_CRITERIA_COVERAGE_TOKEN_PINNED`
- `QM_FULL_DERIVATION_PROGRESS_CYCLE7_v0: UNITARY_EXIT_ROW_PROMOTION_TOKEN_PINNED`
- `QM_FULL_DERIVATION_PROGRESS_CYCLE8_v0: DERIVATION_EXIT_ROW_PROMOTION_TOKEN_PINNED`
- `QM_FULL_DERIVATION_PROGRESS_CYCLE9_v0: ANTICIRCULARITY_EXIT_ROW_PROMOTION_TOKEN_PINNED`
- `QM_FULL_DERIVATION_PROGRESS_CYCLE10_v0: ASSUMPTION_MINIMIZATION_EXIT_ROW_PROMOTION_TOKEN_PINNED`
- `QM_FULL_DERIVATION_PROGRESS_CYCLE11_v0: PREDISCHARGE_GATE_BUNDLE_TOKEN_PINNED`
- `QM_FULL_DERIVATION_PROGRESS_CYCLE12_v0: DISCHARGE_TRANSITION_BUNDLE_TOKEN_PINNED`
- `QM_FULL_DERIVATION_PROGRESS_CYCLE13_v0: KEYB_POLICY_SIGNOFF_SURFACE_TOKEN_PINNED`
- `QM_FULL_DERIVATION_PROGRESS_CYCLE14_v0: TWO_KEY_RELEASE_DISCHARGE_COMPLETED`

Reclassification token:
- `QM_FULL_DERIVATION_RECLASSIFICATION_v0_MIN1: hStepTotalPolicy_POLICY_TO_MATH_via_qm_step_total_of_definition`

Discharge-criteria token:
- `QM_FULL_DERIVATION_DISCHARGE_CRITERIA_v0: CYCLE10_ROW_LEVEL_CRITERIA_PINNED`

Discharge criteria rows (cycle-010 pinned):
1. `QM_FULL_DERIVATION_CRITERIA_ROW_01_v0: EVOLUTION_LAW_DERIVATION_CHAIN_PINNED`
- required theorem tokens:
  - `qm_full_derivation_cycle1_contract_bridge_token_v0`
  - `qm_full_derivation_cycle4_composition_bundle_token_v0`

Exit-row promotion token:
- `QM_FULL_DERIVATION_EXIT_ROW_01_STATUS_v0: DISCHARGED_v0_DERIVATION_GRADE`
- closure theorem witness token:
  - `qm_full_derivation_cycle7_derivation_exit_row_closure_token_v0`

2. `QM_FULL_DERIVATION_CRITERIA_ROW_02_v0: UNITARY_CONSISTENCY_CHAIN_PINNED`
- required theorem token:
  - `qm_full_derivation_cycle2_unitary_consistency_token_v0`

Exit-row promotion token:
- `QM_FULL_DERIVATION_EXIT_ROW_02_STATUS_v0: DISCHARGED_v0_DERIVATION_GRADE`
- closure theorem witness token:
  - `qm_full_derivation_cycle6_unitary_exit_row_closure_token_v0`

3. `QM_FULL_DERIVATION_CRITERIA_ROW_03_v0: ANTI_CIRCULARITY_GUARD_PINNED`
- required guard token:
  - `QM_ANTI_CIRCULARITY_GUARD_v0: NO_DIRECT_SCHRODINGER_INSERTION`

Exit-row promotion token:
- `QM_FULL_DERIVATION_EXIT_ROW_04_STATUS_v0: DISCHARGED_v0_DERIVATION_GRADE`
- closure theorem witness token:
  - `qm_full_derivation_cycle8_anticircularity_exit_row_closure_token_v0`

4. `QM_FULL_DERIVATION_CRITERIA_ROW_04_v0: ASSUMPTION_MINIMIZATION_PINNED`
- required theorem/reclassification tokens:
  - `qm_full_derivation_cycle5_policy_to_math_reclassification_token_v0`
  - `QM_FULL_DERIVATION_RECLASSIFICATION_v0_MIN1: hStepTotalPolicy_POLICY_TO_MATH_via_qm_step_total_of_definition`

Exit-row promotion token:
- `QM_FULL_DERIVATION_EXIT_ROW_03_STATUS_v0: DISCHARGED_v0_DERIVATION_GRADE`
- closure theorem witness token:
  - `qm_full_derivation_cycle9_assumption_minimization_exit_row_closure_token_v0`

5. `QM_FULL_DERIVATION_CRITERIA_ROW_05_v0: STATE_GATE_SYNC_PINNED`
- required synchronization surfaces:
  - `State_of_the_Theory.md`
  - `formal/python/tests/test_qm_gr_regime_expansion_gate.py`

Criteria evidence artifact token:
- `QM_FULL_DERIVATION_DISCHARGE_CRITERIA_ARTIFACT_v0: qm_full_derivation_discharge_criteria_cycle10_v0`
- `QM_FULL_DERIVATION_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0: 3925b71a53f85580e0fc22f48404cae71565b27926629b60aa3f702fe7b41ff1`

Criteria evidence artifact pointer:
- `formal/output/qm_full_derivation_discharge_criteria_cycle10_v0.json`

Exit-criteria coverage artifact token:
- `QM_FULL_DERIVATION_EXIT_CRITERIA_COVERAGE_ARTIFACT_v0: qm_full_derivation_exit_criteria_coverage_cycle14_v0`

Exit-criteria coverage artifact pointer:
- `formal/output/qm_full_derivation_exit_criteria_coverage_cycle14_v0.json`

Pre-discharge gate artifact token:
- `QM_FULL_DERIVATION_PREDISCHARGE_GATE_ARTIFACT_v0: qm_full_derivation_predischarge_gate_cycle19_v0`

Pre-discharge gate artifact pointer:
- `formal/output/qm_full_derivation_predischarge_gate_cycle19_v0.json`

Discharge-transition bundle artifact token:
- `QM_FULL_DERIVATION_DISCHARGE_TRANSITION_BUNDLE_ARTIFACT_v0: qm_full_derivation_discharge_transition_bundle_cycle20_v0`

Discharge-transition bundle artifact pointer:
- `formal/output/qm_full_derivation_discharge_transition_bundle_cycle20_v0.json`

Key-B policy-signoff artifact token:
- `QM_FULL_DERIVATION_KEYB_POLICY_SIGNOFF_ARTIFACT_v0: qm_full_derivation_keyb_policy_signoff_cycle21_v0`

Key-B policy-signoff artifact pointer:
- `formal/output/qm_full_derivation_keyb_policy_signoff_cycle21_v0.json`

Scope boundary:
- v0 derivation program only.
- Schrodinger-form derivation and unitary-consistency closure are discharged at bounded theorem scope under explicit assumptions.
- no Born-rule/measurement-semantics completion claim in this artifact.
- bounded inevitability is discharged at theorem-body bounded scope under explicit dependencies and anti-circularity guards.
- legacy compatibility token retained for gate continuity: no claim of completed Schrodinger derivation in this artifact (superseded by bounded discharged theorem status).
- legacy compatibility token retained for gate continuity: no claim of completed unitary recovery in this artifact (superseded by bounded discharged theorem status).

Required discharge tracks:
1. Evolution-law derivation track:
- derive a Schrodinger-form surface from declared primitive objects, not by direct insertion.

2. Unitary-consistency track:
- show norm-preservation/inner-product consistency under explicit assumptions.

3. Assumption minimization track:
- reduce `POLICY` assumptions by theorem-bound reclassification where possible.

4. Cross-surface synchronization track:
- synchronize target tokens, state tokens, and enforcement gate outputs.

Cycle-001 micro-targets (now pinned):
1. `TARGET-QM-FULL-MICRO-01-CONTRACT-BRIDGE-v0`
- theorem token:
  - `qm_full_derivation_cycle1_contract_bridge_token_v0`
- scope:
  - prove contract-bridge carry-through from `QMEvolutionAssumptions_v0_min1`
    to `QMStateEvolvesUnderContract` without widening claim scope.

Cycle-002 micro-targets (now pinned):
1. `TARGET-QM-FULL-MICRO-02-UNITARY-CONSISTENCY-v0`
- theorem token:
  - `qm_full_derivation_cycle2_unitary_consistency_token_v0`
- scope:
  - pin an explicit unitary-consistency witness surface under declared
    assumptions without claiming completed Schrodinger derivation.

Cycle-003 micro-targets (now pinned):
1. `TARGET-QM-FULL-MICRO-03-ANTI-CIRCULARITY-GUARD-v0`
- theorem token:
  - `qm_full_derivation_cycle3_no_direct_schrodinger_insertion_guard_v0`
- required guard token:
  - `QM_ANTI_CIRCULARITY_GUARD_v0: NO_DIRECT_SCHRODINGER_INSERTION`
- forbidden insertion token:
  - `QM_FORBIDDEN_DIRECT_SCHRODINGER_INSERTION_v0`
- scope:
  - make anti-circularity explicit at scaffold/gate level by pinning a
    no-direct-insertion guard theorem and an explicit forbidden-token check.

Cycle-004 micro-targets (now pinned):
1. `TARGET-QM-FULL-MICRO-04-COMPOSITION-BUNDLE-v0`
- theorem token:
  - `qm_full_derivation_cycle4_composition_bundle_token_v0`
- scope:
  - compose Cycle-001/002/003 surfaces into one auditable bundle theorem under
    explicit assumptions without widening claim scope.

Cycle-005 micro-targets (now pinned):
1. `TARGET-QM-FULL-MICRO-05-ASSUMPTION-MINIMIZATION-v0`
- theorem token:
  - `qm_full_derivation_cycle5_policy_to_math_reclassification_token_v0`
- scope:
  - pin first full-derivation-track policy-to-math reclassification by deriving
    step-total witness from definition-level theorem route.

Canonical pointers:
- `formal/toe_formal/ToeFormal/QM/EvolutionContract.lean`
- `formal/toe_formal/ToeFormal/QM/QMEvolutionAssumptionLedger.lean`
- `formal/toe_formal/ToeFormal/QM/QMFullDerivationScaffold.lean`
- `formal/docs/paper/DERIVATION_TARGET_QM_EVOLUTION_HARDENING_v0.md`

Exit criteria (for future adjudication flip):
- explicit derivation theorem token(s) are pinned,
- unitary-consistency theorem token(s) are pinned,
- assumptions are registry-linked and minimized,
- gate tests assert anti-circularity and no hidden assumptions,
- adjudication synchronized to `DISCHARGED_v0_DERIVATION_GRADE`,
- bounded inevitability synchronized to `DISCHARGED_v0_BOUNDED` with dedicated theorem-body inevitability gate closure pinned.
