# State Claim Traceability Audit v0

Scope: second-pass high-impact claim audit for `State_of_the_Theory.md`.

Method notes:
- High-impact classes used: `Derivation`, `Recovery`, `Inevitability`, `Empirical`, `Cross-pillar`.
- Enforcement buckets: `A` (gate-enforced), `B` (authority-invariant-enforced), `C` (narrative-bounded non-authority discipline), `D` (unenforced risk channel).
- This v0 audit intentionally uses a curated sample (32 entries) to remain tractable and repeatable.

## CLAIM_TRACEABILITY

* ClaimID: SOT-CLAIM-001
* ClaimText: EM scope is bounded and explicitly excludes Standard Model completion and external truth claims.
* Location: State_of_the_Theory.md:L52-L55
* ImpactClass: Cross-pillar
* EnforcementBucket: C
* EnforcingTests: formal/python/tests/test_no_unbounded_claims.py
* EnforcedArtifacts: State_of_the_Theory.md
* Tokens/Invariants: bounded and non-claim posture required for EM kickoff narrative.
* Notes: Narrative discipline claim, intentionally non-promotional.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-002
* ClaimText: EM Cycle-001 remains scaffold-only and not discharged.
* Location: State_of_the_Theory.md:L66-L74
* ImpactClass: Derivation
* EnforcementBucket: A
* EnforcingTests: formal/python/tests/test_em_u1_micro01_template_and_tokens.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_01_OBJECT_SCAFFOLD_v0.md; State_of_the_Theory.md
* Tokens/Invariants: EM_U1_MICRO01_OBJECT_SCAFFOLD_ADJUDICATION must remain NOT_YET_DISCHARGED.
* Notes: Prevents early closure drift.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-003
* ClaimText: EM Cycle-002 gauge-contract theorem surface is assumption-derived but bounded and non-claim.
* Location: State_of_the_Theory.md:L75-L88
* ImpactClass: Derivation
* EnforcementBucket: A
* EnforcingTests: formal/python/tests/test_em_u1_micro02_gauge_contract_surface.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_02_GAUGE_CONTRACT_SURFACE_v0.md; formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean
* Tokens/Invariants: assumption surface and derivation token pin must stay synchronized.
* Notes: Allows theorem-surface evolution without discharge inflation.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-004
* ClaimText: EM Cycle-003 pre-discharge gate bundle is discharged conditional and authorization-gated.
* Location: State_of_the_Theory.md:L89-L106
* ImpactClass: Derivation
* EnforcementBucket: A
* EnforcingTests: formal/python/tests/test_em_u1_micro03_predischarge_gate_bundle.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_03_PREDISCHARGE_GATE_BUNDLE_v0.md; formal/docs/paper/ASSUMPTION_REGISTRY_v1.md
* Tokens/Invariants: EM_U1_MICRO03_PREDISCHARGE_GATE_BUNDLE_ADJUDICATION and assumption-registry sync gates.
* Notes: Enforces staged authorization before later cycle attempts.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-005
* ClaimText: EM Cycle-004 Maxwell-form work is attempt-package only and not discharged.
* Location: State_of_the_Theory.md:L107-L122
* ImpactClass: Recovery
* EnforcementBucket: A
* EnforcingTests: formal/python/tests/test_em_u1_micro04_maxwell_form_attempt_shape.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_04_MAXWELL_FORM_ATTEMPT_PACKAGE_v0.md
* Tokens/Invariants: EM_U1_MICRO04_MAXWELL_FORM_ATTEMPT_ADJUDICATION must stay NOT_YET_DISCHARGED.
* Notes: Prevents Maxwell-shape language from being treated as closure.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-006
* ClaimText: EM Cycle-005 semantics mapping remains definitional-only and no dynamics closure claim.
* Location: State_of_the_Theory.md:L123-L141
* ImpactClass: Recovery
* EnforcementBucket: A
* EnforcingTests: formal/python/tests/test_em_u1_micro05_maxwell_form_semantics_mapping.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_05_MAXWELL_FORM_SEMANTICS_MAPPING_v0.md
* Tokens/Invariants: EM_U1_MAXWELL_SEMANTICS_DEFINITIONAL_ONLY_GATE_v0.
* Notes: Bounded semantic projection, no closure promotion.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-007
* ClaimText: EM Cycle-006 is convention-lock only and no dynamics-layer closure.
* Location: State_of_the_Theory.md:L143-L157
* ImpactClass: Derivation
* EnforcementBucket: A
* EnforcingTests: formal/python/tests/test_em_u1_micro06_convention_lock_3p1.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_06_CONVENTION_LOCK_3P1_v0.md
* Tokens/Invariants: EM_U1_CONVENTION_LOCK_NO_DYNAMICS_v0 and adjudication token.
* Notes: Conventions are frozen without implying derivation completion.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-008
* ClaimText: EM Cycle-007 import lanes are placeholder-only and assumption-ID gated.
* Location: State_of_the_Theory.md:L157-L176
* ImpactClass: Derivation
* EnforcementBucket: A
* EnforcingTests: formal/python/tests/test_em_u1_micro07_import_lanes_placeholders.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_07_IMPORT_LANES_PLACEHOLDERS_v0.md; formal/docs/paper/ASSUMPTION_REGISTRY_v1.md
* Tokens/Invariants: EM_U1_IMPORT_LANES_NO_DYNAMICS_v0 and assumption-ID gate.
* Notes: Explicitly prevents hidden import-to-closure jumps.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-009
* ClaimText: EM Cycle-008 interface contracts define lanes but do not authorize unit/gauge selection.
* Location: State_of_the_Theory.md:L177-L196
* ImpactClass: Derivation
* EnforcementBucket: A
* EnforcingTests: formal/python/tests/test_em_u1_micro08_import_lanes_interface_contracts.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_08_IMPORT_LANES_INTERFACE_CONTRACTS_v0.md
* Tokens/Invariants: EM_U1_IMPORT_LANES_INTERFACE_NO_SELECTION_v0.
* Notes: Keeps interface-level language non-promotional.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-010
* ClaimText: EM Cycle-009 dual/hodge section is convention-lock only, no Maxwell closure claim.
* Location: State_of_the_Theory.md:L197-L217
* ImpactClass: Recovery
* EnforcementBucket: A
* EnforcingTests: formal/python/tests/test_em_u1_micro09_dual_hodge_convention_lock.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_09_DUAL_HODGE_CONVENTION_LOCK_v0.md
* Tokens/Invariants: EM_U1_DUAL_HODGE_NO_DYNAMICS_v0.
* Notes: Definitional layer is explicitly separated from derivational closure.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-011
* ClaimText: EM Cycle-011 Maxwell equation surfaces are statement-only and not derivation claims.
* Location: State_of_the_Theory.md:L238-L258
* ImpactClass: Recovery
* EnforcementBucket: A
* EnforcingTests: formal/python/tests/test_em_u1_micro11_maxwell_equation_surfaces_statement_lock.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_11_MAXWELL_EQUATION_SURFACES_STATEMENT_LOCK_v0.md
* Tokens/Invariants: EM_U1_MAXWELL_SURFACE_NO_DERIVATION_v0 and adjudication token.
* Notes: Statement surfaces remain non-promotional.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-012
* ClaimText: EM Cycle-013 tensor/forms compatibility map is statement-only, no derivation promotion.
* Location: State_of_the_Theory.md:L286-L306
* ImpactClass: Recovery
* EnforcementBucket: A
* EnforcingTests: formal/python/tests/test_em_u1_micro13_maxwell_tensor_forms_compatibility_map.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_13_MAXWELL_TENSOR_FORMS_COMPATIBILITY_MAP_v0.md
* Tokens/Invariants: EM_U1_MAXWELL_COMPATIBILITY_NO_DERIVATION_v0.
* Notes: Compatibility map cannot become closure evidence on its own.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-013
* ClaimText: EM Cycle-016 route package is attempt-only and explicitly non-derivational.
* Location: State_of_the_Theory.md:L365-L389
* ImpactClass: Derivation
* EnforcementBucket: A
* EnforcingTests: formal/python/tests/test_em_u1_micro16_maxwell_to_continuity_route_attempt_package.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_16_MAXWELL_TO_CONTINUITY_ROUTE_ATTEMPT_PACKAGE_v0.md
* Tokens/Invariants: EM_U1_MAXWELL_CONTINUITY_NO_DERIVATION_v0.
* Notes: Prevents continuity-route overclaiming.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-014
* ClaimText: EM Cycle-018 theorem attempt is no-promotion and no-discharge.
* Location: State_of_the_Theory.md:L417-L440
* ImpactClass: Derivation
* EnforcementBucket: A
* EnforcingTests: formal/python/tests/test_em_u1_micro18_maxwell_to_continuity_theorem_attempt_package.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_18_MAXWELL_TO_CONTINUITY_THEOREM_ATTEMPT_PACKAGE_v0.md
* Tokens/Invariants: EM_U1_MAXWELL_CONTINUITY_THEOREM_NO_PROMOTION_v0.
* Notes: Keeps theorem-attempt semantics bounded.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-015
* ClaimText: EM Cycle-024 route-closure attempt is bounded and explicitly blocks inevitability promotion.
* Location: State_of_the_Theory.md:L600-L611
* ImpactClass: Inevitability
* EnforcementBucket: A
* EnforcingTests: formal/python/tests/test_em_u1_micro24_maxwell_to_continuity_route_closure_attempt_package.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_24_MAXWELL_TO_CONTINUITY_ROUTE_CLOSURE_ATTEMPT_PACKAGE_v0.md
* Tokens/Invariants: EM_U1_MAXWELL_CONTINUITY_ROUTE_CLOSURE_BOUNDARY_v0.
* Notes: Explicit anti-inevitability guard.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-016
* ClaimText: EM Cycle-028 DD-subroute composition is attempt-only and cannot promote to full discharge.
* Location: State_of_the_Theory.md:L743-L754
* ImpactClass: Derivation
* EnforcementBucket: A
* EnforcingTests: formal/python/tests/test_em_u1_micro28_maxwell_to_continuity_dd_subroute_composition_attempt.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_28_MAXWELL_TO_CONTINUITY_DD_SUBROUTE_COMPOSITION_ATTEMPT_v0.md
* Tokens/Invariants: EM_U1_MAXWELL_CONTINUITY_DD_SUBROUTE_COMPOSITION_NO_PROMOTION_v0.
* Notes: Subroute composition remains bounded attempt language.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-017
* ClaimText: EM Cycle-029 typed augmentation is attempt-only and bounded against inevitability promotion.
* Location: State_of_the_Theory.md:L790-L801
* ImpactClass: Inevitability
* EnforcementBucket: A
* EnforcingTests: formal/python/tests/test_em_u1_micro29_maxwell_to_continuity_typed_dd_subroute_augmentation_attempt.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_29_MAXWELL_TO_CONTINUITY_TYPED_DD_SUBROUTE_AUGMENTATION_ATTEMPT_v0.md
* Tokens/Invariants: EM_U1_MAXWELL_CONTINUITY_TYPED_DD_SUBROUTE_AUGMENTATION_BOUNDARY_v0.
* Notes: Prevents typed-route inflation into closure rhetoric.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-018
* ClaimText: EM Cycle-030 typed-route consumer remains non-claim and non-promotional.
* Location: State_of_the_Theory.md:L832-L843
* ImpactClass: Derivation
* EnforcementBucket: A
* EnforcingTests: formal/python/tests/test_em_u1_micro30_maxwell_to_continuity_typed_route_consumer_attempt.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_30_MAXWELL_TO_CONTINUITY_TYPED_ROUTE_CONSUMER_ATTEMPT_v0.md
* Tokens/Invariants: EM_U1_MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_NO_PROMOTION_v0.
* Notes: Consumer route cannot imply theorem-grade closure.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-019
* ClaimText: Pillar-GR full-derivation discharge status is synchronized as DISCHARGED_v0_DISCRETE.
* Location: State_of_the_Theory.md:L882-L887
* ImpactClass: Cross-pillar
* EnforcementBucket: B
* EnforcingTests: formal/python/tests/test_pillar_adjudication_cross_surface_consistency_gate.py; formal/python/tests/test_pillar_status_matrix_consistency_gate.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md; formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json; formal/docs/paper/PHYSICS_ROADMAP_v0.md
* Tokens/Invariants: matrix full_derivation value must match discharge/state/roadmap tokens.
* Notes: Cross-surface invariant for GR status truth.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-020
* ClaimText: Pillar-QM full-derivation discharge status is synchronized as DISCHARGED_v0_DERIVATION_GRADE.
* Location: State_of_the_Theory.md:L890-L895
* ImpactClass: Cross-pillar
* EnforcementBucket: B
* EnforcingTests: formal/python/tests/test_pillar_adjudication_cross_surface_consistency_gate.py; formal/python/tests/test_pillar_status_matrix_consistency_gate.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0.md; formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json; formal/docs/paper/PHYSICS_ROADMAP_v0.md
* Tokens/Invariants: matrix full_derivation value must match discharge/state/roadmap tokens.
* Notes: Cross-surface invariant for QM status truth.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-021
* ClaimText: Pillar-EM full-derivation discharge status is synchronized as DISCHARGED_v0_DERIVATION_GRADE.
* Location: State_of_the_Theory.md:L898-L903
* ImpactClass: Cross-pillar
* EnforcementBucket: B
* EnforcingTests: formal/python/tests/test_pillar_adjudication_cross_surface_consistency_gate.py; formal/python/tests/test_pillar_status_matrix_consistency_gate.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md; formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json; formal/docs/paper/PHYSICS_ROADMAP_v0.md
* Tokens/Invariants: matrix full_derivation value must match discharge/state/roadmap tokens.
* Notes: Cross-surface invariant for EM status truth.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-022
* ClaimText: EM full-discharge row-level exits are non-blocked and discharged for rows 01/02.
* Location: State_of_the_Theory.md:L909-L910
* ImpactClass: Cross-pillar
* EnforcementBucket: A
* EnforcingTests: formal/python/tests/test_pillar_full_discharge_completion_mechanics.py; formal/python/tests/test_em_u1_full_discharge_adjudication_criteria_artifact.py
* EnforcedArtifacts: formal/output/em_pillar_full_discharge_adjudication_criteria_cycle46_v0.json; State_of_the_Theory.md
* Tokens/Invariants: EM_PILLAR_FULL_DISCHARGE_EXIT_ROW_01_STATUS_v0 and ROW_02 status tokens.
* Notes: Exit-row discharge claim requires artifact and gate alignment.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-023
* ClaimText: GR conservation compatibility and gate posture are synchronized to CLOSED/ALLOWED statuses.
* Location: State_of_the_Theory.md:L943-L948
* ImpactClass: Cross-pillar
* EnforcementBucket: B
* EnforcingTests: formal/python/tests/test_pillar_adjudication_cross_surface_consistency_gate.py; formal/python/tests/test_pillar_status_matrix_consistency_gate.py
* EnforcedArtifacts: formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json; formal/docs/paper/PHYSICS_ROADMAP_v0.md; State_of_the_Theory.md
* Tokens/Invariants: PILLAR-GR_PHYSICS_STATUS, PILLAR-GR_GOVERNANCE_STATUS, PROCEED_GATE_GR, MATRIX_CLOSURE_GATE_GR.
* Notes: Multi-token state consistency across authority surfaces.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-024
* ClaimText: GR full derivation is T-PROVED with bounded inevitability adjudication.
* Location: State_of_the_Theory.md:L959-L964
* ImpactClass: Inevitability
* EnforcementBucket: B
* EnforcingTests: formal/python/tests/test_pillar_adjudication_cross_surface_consistency_gate.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md; formal/docs/paper/PHYSICS_ROADMAP_v0.md; State_of_the_Theory.md
* Tokens/Invariants: FULL_DERIVATION_ADJUDICATION and FULL_DERIVATION_INEVITABILITY_ADJUDICATION values must match surfaces.
* Notes: Bounded inevitability semantics are explicitly encoded in token values.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-025
* ClaimText: GR discharged state is bounded by explicit no-continuum/no-uniqueness/no-Noether-family boundaries.
* Location: State_of_the_Theory.md:L949-L952
* ImpactClass: Inevitability
* EnforcementBucket: C
* EnforcingTests: formal/python/tests/test_no_unbounded_claims.py
* EnforcedArtifacts: State_of_the_Theory.md
* Tokens/Invariants: explicit textual boundary list retained in authority narrative.
* Notes: Narrative bounding claim, not a token flip claim.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-026
* ClaimText: QFT full derivation adjudication is DISCHARGED_v0 on active authority surface.
* Location: State_of_the_Theory.md:L1620
* ImpactClass: Cross-pillar
* EnforcementBucket: B
* EnforcingTests: formal/python/tests/test_qft_full_derivation_adjudication_consistency_gate.py; formal/python/tests/test_pillar_adjudication_cross_surface_consistency_gate.py; formal/python/tests/test_pillar_status_matrix_consistency_gate.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md; formal/docs/paper/PHYSICS_ROADMAP_v0.md; formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json; State_of_the_Theory.md
* Tokens/Invariants: QFT_FULL_DERIVATION_ADJUDICATION equality across authority surfaces.
* Notes: Primary QFT status-truth contract.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-027
* ClaimText: QFT inevitability adjudication is DISCHARGED_v0 on active authority surface.
* Location: State_of_the_Theory.md:L1621
* ImpactClass: Inevitability
* EnforcementBucket: B
* EnforcingTests: formal/python/tests/test_qft_full_derivation_adjudication_consistency_gate.py; formal/python/tests/test_pillar_adjudication_cross_surface_consistency_gate.py; formal/python/tests/test_pillar_status_matrix_consistency_gate.py
* EnforcedArtifacts: formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md; formal/docs/paper/PHYSICS_ROADMAP_v0.md; formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json; State_of_the_Theory.md
* Tokens/Invariants: QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION equality across authority surfaces.
* Notes: Inevitability state is versioned and cross-surface synchronized.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-028
* ClaimText: QFT nonflip readiness scope confirms adjudication remains discharged while preserving explicit flip authorization requirements.
* Location: State_of_the_Theory.md:L1629-L1632
* ImpactClass: Cross-pillar
* EnforcementBucket: A
* EnforcingTests: formal/python/tests/test_qft_full_derivation_nonflip_execution_readiness_packet_cycle55_gate.py
* EnforcedArtifacts: formal/output/qft_full_derivation_nonflip_execution_readiness_packet_cycle55_v0.json; State_of_the_Theory.md
* Tokens/Invariants: QFT_FULL_DERIVATION_NONFLIP_EXECUTION_READINESS_PACKET_SCOPE_v0 token and packet artifact linkage.
* Notes: Enforces nonflip semantics despite discharged posture.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-029
* ClaimText: Archived legacy QFT NOT_YET tokens are fenced as non-authority history.
* Location: State_of_the_Theory.md:L1634-L1640
* ImpactClass: Cross-pillar
* EnforcementBucket: B
* EnforcingTests: formal/python/tests/test_archived_history_sentinel_integrity_gate.py; formal/python/tests/test_qft_full_derivation_legacy_retirement_gate.py; formal/python/tests/test_pillar_adjudication_legacy_retirement_gate.py
* EnforcedArtifacts: State_of_the_Theory.md; formal/docs/paper/PHYSICS_ROADMAP_v0.md; formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md
* Tokens/Invariants: sentinel-bounded archive-only presence for legacy NOT_YET tokens.
* Notes: Historical retention without active-authority leakage.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-030
* ClaimText: Authority tokens must be single-definition on active surfaces and not duplicated via archive leakage.
* Location: State_of_the_Theory.md:L1620-L1634
* ImpactClass: Cross-pillar
* EnforcementBucket: B
* EnforcingTests: formal/python/tests/test_authority_token_single_definition_gate.py; formal/python/tests/test_archived_history_sentinel_integrity_gate.py
* EnforcedArtifacts: State_of_the_Theory.md; formal/docs/paper/PHYSICS_ROADMAP_v0.md; formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md
* Tokens/Invariants: single-definition and active-vs-archived structural partitioning.
* Notes: Prevents contradictory token authority in one surface.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-031
* ClaimText: Legacy token migration windows are governed structurally via sentinel-aware active text extraction.
* Location: State_of_the_Theory.md:L1634-L1660
* ImpactClass: Cross-pillar
* EnforcementBucket: B
* EnforcingTests: formal/python/tests/test_token_migration_window_gate.py
* EnforcedArtifacts: State_of_the_Theory.md; formal/docs/paper/PHYSICS_ROADMAP_v0.md; formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md
* Tokens/Invariants: migration checks operate on active region only.
* Notes: Reduces false positives/negatives from historical snapshots.
* Fix (if D): N/A

* ClaimID: SOT-CLAIM-032
* ClaimText: Sentinel fence structure itself is mandatory and ordered for archived history in authority docs.
* Location: State_of_the_Theory.md:L1634; State_of_the_Theory.md:L8161
* ImpactClass: Cross-pillar
* EnforcementBucket: B
* EnforcingTests: formal/python/tests/test_archived_history_sentinel_integrity_gate.py
* EnforcedArtifacts: State_of_the_Theory.md; formal/docs/paper/PHYSICS_ROADMAP_v0.md; formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md
* Tokens/Invariants: exactly one start sentinel and one end sentinel in correct order with non-empty archive block.
* Notes: Structural anti-hallucination guard for active authority parsing.
* Fix (if D): N/A

Summary:
- Entries audited: 32
- Bucket counts: A=16, B=13, C=3, D=0
- Immediate D remediations required: none in this v0 sample.
