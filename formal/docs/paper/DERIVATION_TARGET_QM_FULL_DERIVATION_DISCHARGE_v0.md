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

- `TARGET-QM-FULL-DERIVATION-DISCHARGE-v0` remains the frozen target surface.
- Standardized pillar discharge target ID:
  - `TARGET-PILLAR-QM-FULL-DERIVATION-DISCHARGE-v0`

## ASSUMPTION_FREEZE section

- Minimized-assumption anchor remains explicit: `QMInevitabilityMinimizedAssumptions_v0`.
- Required named-route assumptions remain explicit and theorem-linked.
- Canonical assumption classes and minimized-assumption anchor are frozen in this discharge lane.

## CANONICAL_ROUTE section

- Canonical constructive route remains explicit and anti-circularity guarded.
- Direct Schrodinger insertion remains forbidden on the canonical route.
- Canonical discharge route remains constructive, theorem-linked, and anti-circular.

## ANTI_SHORTCUT section

- No-shortcut posture remains mandatory:
  - no direct Schrodinger insertion route,
  - no compatibility-wrapper-only closure promotion.

## COUNTERFACTUAL section

- Counterfactual break token remains explicit: `¬QMInevitabilityClosureSurface_v0`.
- Per-assumption counterfactual break theorem tokens remain pinned.
- Counterfactual break surfaces remain explicit and required for discharge-lane integrity.

## INDEPENDENT_NECESSITY section

- Structural classification anchor remains explicit:
  `QMInevitabilityConstructiveRouteClassification_v0`.
- Independent-necessity classification remains theorem-linked and non-circular.

## BOUNDED_SCOPE section

- non-claim boundary remains explicit and binding for this artifact.
- bounded theorem-body scope only; no Born-rule/measurement-semantics completion claim and no external truth claim.

## HARDENING section

- Discharge-lane hardening requires synchronized target/state/results/roadmap surfaces with anti-circular guards.

- bounded non-claim discharge lane only; no Born-rule completion or measurement-semantics completion promotion.

## DRIFT_GATES section

- Standardized pillar discharge lane tokens:
  - `PILLAR_QM_FULL_DERIVATION_DISCHARGE_LOCALIZATION_GATE_v0: FULL_DISCHARGE_ARTIFACTS_ONLY`
  - `PILLAR_QM_FULL_DERIVATION_DISCHARGE_NO_PROMOTION_v0: DISCHARGED_NO_AUTOMATIC_PROMOTION`
  - `PILLAR_QM_FULL_DERIVATION_DISCHARGE_BOUNDARY_v0: NO_FULL_DERIVATION_DISCHARGE_OR_INEVITABILITY_PROMOTION`

## ADJUDICATION_SYNC section

- Standardized pillar discharge adjudication token:
  - `PILLAR_QM_FULL_DERIVATION_DISCHARGE_ADJUDICATION: DISCHARGED_v0_DERIVATION_GRADE`
- Intentional umbrella/discharge equivalence token:
  - `PILLAR_QM_DISCHARGE_DOC_IS_UMBRELLA_DOC_v0: TRUE`
- Registry pointer:
  - `formal/docs/paper/DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0.md`
  - `formal/docs/paper/PILLAR_DISCHARGE_REGISTRY_v0.json`

- External-lane evidence checkpoint coupling bundle (bounded non-claim):
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE01_ARTIFACT_v0: qm_external_lane_evidence_checkpoint_cycle01_v0`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE01_SHA256_v0: c0e011e1c73ea5fa555ed965c62488a24d0506cc9acf61f02f1d0a762a160ec5`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE01_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
  - `formal/output/qm_external_lane_evidence_checkpoint_cycle01_v0.json`
  - `formal/python/tests/test_qm_external_lane_evidence_checkpoint_coupling_gate.py`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE02_ARTIFACT_v0: qm_external_lane_evidence_checkpoint_cycle02_v0`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE02_SHA256_v0: ee514df5bf48bdc509fc726a775cdaab4a731b52a02b362e39e55c9b70a40019`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE02_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
  - `formal/output/qm_external_lane_evidence_checkpoint_cycle02_v0.json`
  - `formal/python/tests/test_qm_external_lane_evidence_checkpoint_coupling_cycle02_gate.py`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE03_ARTIFACT_v0: qm_external_lane_evidence_checkpoint_cycle03_v0`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE03_SHA256_v0: 277bc3e338f88e332cc2967a5d268cac4ada32f0e678be45806b5c86d86741c9`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE03_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
  - `formal/output/qm_external_lane_evidence_checkpoint_cycle03_v0.json`
  - `formal/python/tests/test_qm_external_lane_evidence_checkpoint_coupling_cycle03_gate.py`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE04_ARTIFACT_v0: qm_external_lane_evidence_checkpoint_cycle04_v0`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE04_SHA256_v0: 0eb3bbc0747847bf15d4ac5cbd707a3b7181bba45b94679abbb62f09ae185d2d`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE04_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
  - `formal/output/qm_external_lane_evidence_checkpoint_cycle04_v0.json`
  - `formal/python/tests/test_qm_external_lane_evidence_checkpoint_coupling_cycle04_gate.py`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE05_ARTIFACT_v0: qm_external_lane_evidence_checkpoint_cycle05_v0`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE05_SHA256_v0: 049810330058bf5a956b01712f0f3a71b7d10721b90aeb7058ceea721b9a053e`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE05_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
  - `formal/output/qm_external_lane_evidence_checkpoint_cycle05_v0.json`
  - `formal/python/tests/test_qm_external_lane_evidence_checkpoint_coupling_cycle05_gate.py`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE06_ARTIFACT_v0: qm_external_lane_evidence_checkpoint_cycle06_v0`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE06_SHA256_v0: 1a57390222d1fd927342661dc5aa8fe1913c7848775af1d28734da0abeb6d0ac`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE06_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
  - `formal/output/qm_external_lane_evidence_checkpoint_cycle06_v0.json`
  - `formal/python/tests/test_qm_external_lane_evidence_checkpoint_coupling_cycle06_gate.py`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE07_ARTIFACT_v0: qm_external_lane_evidence_checkpoint_cycle07_v0`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE07_SHA256_v0: b6b486d5ed9160e6f55b71af12ac4b54f1f304071e60163ac575067f7e8e03c7`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE07_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
  - `formal/output/qm_external_lane_evidence_checkpoint_cycle07_v0.json`
  - `formal/python/tests/test_qm_external_lane_evidence_checkpoint_coupling_cycle07_gate.py`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE08_ARTIFACT_v0: qm_external_lane_evidence_checkpoint_cycle08_v0`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE08_SHA256_v0: 9f21b723c9bde134b03a9f6de1a457affc30196944a984212fbb8b29e11c9f4c`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE08_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
  - `formal/output/qm_external_lane_evidence_checkpoint_cycle08_v0.json`
  - `formal/python/tests/test_qm_external_lane_evidence_checkpoint_coupling_cycle08_gate.py`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE09_ARTIFACT_v0: qm_external_lane_evidence_checkpoint_cycle09_v0`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE09_SHA256_v0: b041f3756cb0a32b8fd5df76610b7ca3f4ca6bef2a8b50c5dd6659cfb0bc4e1a`
  - `QM_EXTERNAL_LANE_EVIDENCE_CHECKPOINT_CYCLE09_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
  - `formal/output/qm_external_lane_evidence_checkpoint_cycle09_v0.json`
  - `formal/python/tests/test_qm_external_lane_evidence_checkpoint_coupling_cycle09_gate.py`

- QM first discriminator scaffold bundle (bounded non-claim):
  - `EMP_QM_01_DISCRIMINATOR_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`
  - `EMP_QM_01_PRUNE_DECISION_v0: ELIMINATION_READY_BOUNDED_v0`
  - `EMP_QM_01_PRUNE_RESULT_v0: PASS_AND_PRUNE_SIGNAL_PRESENT_v0`
  - `EMP_QM_01_ARTIFACT_v0: qm_empirical_discriminator_emp_qm_01_run_cycle02_v0`
  - `EMP_QM_01_ARTIFACT_SHA256_v0: 5fad6fdfaa020303fd912dd5d1f31c112457d0978dffaefd7fd3c9c001da17f5`
  - `EMP_QM_01_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
  - `formal/docs/paper/DERIVATION_TARGET_QM_EMPIRICAL_DISCRIMINATOR_EMP_QM_01_v0.md`
  - `formal/output/qm_empirical_discriminator_emp_qm_01_run_cycle02_v0.json`
  - `formal/python/tests/test_qm_empirical_discriminator_emp_qm_01_scaffold_gate.py`

- QM M2 analytic completeness scaffold bundle (bounded non-claim):
  - `QM_M2_ANALYTIC_COMPLETENESS_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`
  - `QM_M2_ANALYTIC_COMPLETENESS_ARTIFACT_v0: qm_m2_analytic_completeness_scaffold_cycle01_v0`
  - `QM_M2_ANALYTIC_COMPLETENESS_SHA256_v0: 192432c694de481ae9c34b073ebcd214dacfd1ce1b0adc6799697c82bb9d301e`
  - `QM_M2_ANALYTIC_COMPLETENESS_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
  - `formal/output/qm_m2_analytic_completeness_scaffold_cycle01_v0.json`
  - `formal/python/tests/test_qm_m2_analytic_completeness_scaffold_cycle01_gate.py`

- QM M2 canonical equivalence scaffold bundle (bounded non-claim):
  - `QM_M2_CANONICAL_EQUIVALENCE_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`
  - `QM_M2_CANONICAL_EQUIVALENCE_ARTIFACT_v0: qm_m2_canonical_equivalence_scaffold_cycle01_v0`
  - `QM_M2_CANONICAL_EQUIVALENCE_SHA256_v0: 0b5e239151028bb4920840b24ad9f1f6a3fdb44dc39437ff9b3269aadea638ae`
  - `QM_M2_CANONICAL_EQUIVALENCE_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
  - `formal/output/qm_m2_canonical_equivalence_scaffold_cycle01_v0.json`
  - `formal/python/tests/test_qm_m2_canonical_equivalence_scaffold_cycle01_gate.py`

- QM M2 assumption minimization scaffold bundle (bounded non-claim):
  - `QM_M2_ASSUMPTION_MINIMIZATION_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`
  - `QM_M2_ASSUMPTION_MINIMIZATION_ARTIFACT_v0: qm_m2_assumption_minimization_scaffold_cycle01_v0`
  - `QM_M2_ASSUMPTION_MINIMIZATION_SHA256_v0: c32ac32cebd7443e046aedef3fdbccb97661936ee7c5fd61741aef6cf68a07ba`
  - `QM_M2_ASSUMPTION_MINIMIZATION_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
  - `formal/output/qm_m2_assumption_minimization_scaffold_cycle01_v0.json`
  - `formal/python/tests/test_qm_m2_assumption_minimization_scaffold_cycle01_gate.py`

- QM M2 literature alignment scaffold bundle (bounded non-claim):
  - `QM_M2_LITERATURE_ALIGNMENT_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`
  - `QM_M2_LITERATURE_ALIGNMENT_ARTIFACT_v0: qm_m2_literature_alignment_scaffold_cycle01_v0`
  - `QM_M2_LITERATURE_ALIGNMENT_SHA256_v0: 8eecd039c5ecf244054b8727a61835f2f8261d08d875aae945699477c14c3332`
  - `QM_M2_LITERATURE_ALIGNMENT_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
  - `formal/output/qm_m2_literature_alignment_scaffold_cycle01_v0.json`
  - `formal/python/tests/test_qm_m2_literature_alignment_scaffold_cycle01_gate.py`

- QM M2 completion promotion bundle (bounded non-claim):
  - `QM_M2_STATUS_v0: COMPLETE_BOUNDED_v0`
  - `QM_M2_COMPLETION_ARTIFACT_v0: qm_m2_completion_promotion_cycle01_v0`
  - `QM_M2_COMPLETION_SHA256_v0: ed9b3fb5bdf9899076a487a6b840368f6c5b58403632c1706948314330fc4cdb`
  - `QM_M2_COMPLETION_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
  - `formal/output/qm_m2_completion_promotion_cycle01_v0.json`
  - `formal/python/tests/test_qm_m2_completion_promotion_cycle01_gate.py`

- QM M3 completion promotion bundle (bounded non-claim):
  - `QM_M3_STATUS_v0: COMPLETE_BOUNDED_v0`
  - `QM_M3_COMPLETION_ARTIFACT_v0: qm_m3_completion_promotion_cycle01_v0`
  - `QM_M3_COMPLETION_SHA256_v0: 55ae0f9927e8f3bfb39754e0732361ffce7bf8e90235e67c6827e8ea903ee0d0`
  - `QM_M3_COMPLETION_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
  - `QM_M3_PROMOTION_READINESS_v0: FIRST_DISCRIMINATOR_CLOSED_AND_PROMOTED_v0`
  - `formal/docs/paper/DERIVATION_TARGET_QM_M3_COMPLETION_PROMOTION_v0.md`
  - `formal/output/qm_m3_completion_promotion_cycle01_v0.json`
  - `formal/python/tests/test_qm_m3_completion_promotion_cycle01_gate.py`

- QM M4 seam-closure promotion bundle (bounded non-claim):
  - `QM_M4_STATUS_v0: COMPLETE_BOUNDED_v0`
  - `QM_M4_PROMOTION_READINESS_v0: CROSS_PILLAR_SEAM_BUNDLE_PINNED_v0`
  - `QM_M4_SEAM_CLOSURE_ARTIFACT_v0: qm_m4_seam_closure_promotion_cycle01_v0`
  - `QM_M4_SEAM_CLOSURE_SHA256_v0: 6958fd41d0e8a413c0cbe304d17a4ec06807bb799f4d606fd41b86dc1436c3ad`
  - `QM_M4_SEAM_CLOSURE_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
  - `formal/docs/paper/DERIVATION_TARGET_QM_M4_SEAM_CLOSURE_PROMOTION_v0.md`
  - `formal/output/qm_m4_seam_closure_promotion_cycle01_v0.json`
  - `formal/python/tests/test_qm_m4_seam_closure_promotion_cycle01_gate.py`

- Closure-hardening bundle (bounded non-claim):
  - `QM_CLOSURE_HARDENING_BUNDLE_CYCLE01_ARTIFACT_v0: qm_closure_hardening_bundle_cycle01_v0`
  - `QM_CLOSURE_HARDENING_BUNDLE_CYCLE01_SHA256_v0: 00febafaaee38d6a0ba5492fabd7a6b578a417060c16d129ba6886d0cd02af77`
  - `QM_CLOSURE_HARDENING_BUNDLE_CYCLE01_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
  - `formal/output/qm_closure_hardening_bundle_cycle01_v0.json`
  - `formal/python/tests/test_qm_closure_hardening_bundle_coupling_cycle01_gate.py`

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
- `QM_FULL_DERIVATION_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0: 3dddcb3e5928507fe04bb7427d39838af8363395a9d9a8f2a52480d8c031f13a`

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

