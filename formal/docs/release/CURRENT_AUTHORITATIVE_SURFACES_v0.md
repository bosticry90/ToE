# Current Authoritative Surfaces v0

Spec ID:
- `CURRENT_AUTHORITATIVE_SURFACES_v0`

Classification:
- `P-POLICY`

Purpose:
- Provide a human-facing index for the current live authority chain.
- Identify canonical sources for live target, axiom posture, result tokens, nonclaim boundaries, validation commands, and historical-only artifacts.

Current live control state:
- `CURRENT_LIVE_NEXT_TARGET_v0: return_to_full_pillar_target_map_next_lane_selection`
- `PREVIOUS_LIVE_NEXT_TARGET_v0: select_next_post_status_surface_enforcement_bounded_attack`
- `ACTIVE_LANE_v0: post_status_surface_enforcement_bounded_attack_selection`
- `CURRENT_LIVE_TARGET_AUTHORITY_v0: formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json`
- `CURRENT_LIVE_TARGET_FRONTIER_MIRROR_v0: formal/toe_formal/ToeFormal/Derivation/CrossPillarClosureFrontier.lean`
- `CURRENT_LIVE_TARGET_EVIDENCE_v0: formal/toe_formal/ToeFormal/Derivation/PostStatusSurfaceEnforcementBoundedAttackSelection.lean`

Current result-token chain:
- `formal/toe_formal/ToeFormal/Derivation/ReadOnlyValidationHygiene.lean`
- `formal/toe_formal/ToeFormal/Derivation/PostReadOnlyValidationHygieneBoundedAttackSelection.lean`
- `formal/toe_formal/ToeFormal/Derivation/FullPillarTargetMapNextLaneSelectionAfterReadOnlyHygiene.lean`
- `formal/toe_formal/ToeFormal/Derivation/ArtifactRetentionEnforcementPlan.lean`
- `formal/toe_formal/ToeFormal/Derivation/ArtifactRetentionEnforcementPlanResultReview.lean`
- `formal/toe_formal/ToeFormal/Derivation/PostArtifactRetentionEnforcementBoundedAttackSelection.lean`
- `formal/toe_formal/ToeFormal/Derivation/StatusSurfaceCanonicalizationPlan.lean`
- `formal/toe_formal/ToeFormal/Derivation/StatusSurfaceCanonicalizationPlanResultReview.lean`
- `formal/toe_formal/ToeFormal/Derivation/PostStatusSurfaceCanonicalizationBoundedAttackSelection.lean`
- `formal/toe_formal/ToeFormal/Derivation/StatusSurfaceCanonicalizationEnforcementPacket.lean`
- `formal/toe_formal/ToeFormal/Derivation/StatusSurfaceCanonicalizationEnforcementPacketResultReview.lean`
- `formal/toe_formal/ToeFormal/Derivation/PostStatusSurfaceEnforcementBoundedAttackSelection.lean`
- `MASTER_ACTION_DEPENDENCY_GAP_PACKET_RESULT_REVIEW_CONSUMED_NONPROMOTED`
- `POST_MASTER_ACTION_GAP_PACKET_NEXT_ATTACK_SELECTED`
- `FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_GAP_PACKET_REVIEW`
- `READ_ONLY_VALIDATION_HYGIENE_ENFORCED`
- `POST_READ_ONLY_VALIDATION_HYGIENE_NEXT_ATTACK_SELECTED`
- `FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_READ_ONLY_HYGIENE`
- `ARTIFACT_RETENTION_ENFORCEMENT_PLAN_PREPARED`
- `ARTIFACT_RETENTION_ENFORCEMENT_PLAN_RESULT_REVIEW_CONSUMED`
- `POST_ARTIFACT_RETENTION_ENFORCEMENT_NEXT_ATTACK_SELECTED`
- `STATUS_SURFACE_CANONICALIZATION_PLAN_PREPARED`
- `STATUS_SURFACE_CANONICALIZATION_PLAN_RESULT_REVIEW_CONSUMED`
- `POST_STATUS_SURFACE_CANONICALIZATION_NEXT_ATTACK_SELECTED`
- `STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PACKET_PREPARED`
- `STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PACKET_RESULT_REVIEW_CONSUMED`
- `POST_STATUS_SURFACE_ENFORCEMENT_NEXT_ATTACK_SELECTED`

Current status-surface authority classes:
- `CANONICAL_CONTROL_SOURCES: formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json`
- `PUBLIC_SUMMARY_SURFACES: README.md; State_of_the_Theory.md; formal/docs/paper/PHYSICS_ROADMAP_v0.md; formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md`
- `ACTIVE_TARGET_MIRROR_SURFACES: formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md; formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md`
- `GENERATED_OUTPUT_SURFACES: formal/output`
- `HISTORICAL_SUPERSEDED_SURFACES: formal/docs/release historical packet reports unless referenced by the live registry`

Current axiom and proof-debt authority:
- `LEAN_AXIOM_LEDGER_AUTHORITY_v0: formal/docs/release/LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md`
- `REAL_AXIOM_COUNT_v0: 60`
- `REAL_SORRY_OR_ADMIT_COUNT_v0: 0`
- `defaultNonAlias: absent_from_unresolved_axiom_debt_and_lean_backed`
- `sampleRep32: retained_spec_backed_axiom`

Current nonclaim boundary:
- `QFT_GR_SOURCE_MAP_CLOSURE_AUTHORIZED_v0: false`
- `MASTER_ACTION_PROMOTION_AUTHORIZED_v0: false`
- `PILLAR_COMPLETION_INFERRED_v0: false`
- `SEAM_CLOSURE_CLAIM_v0: false`
- `PHASE2_READINESS_CLAIM_v0: false`
- `EMPIRICAL_ADEQUACY_CLAIM_v0: false`
- `CANONICAL_TOE_CLAIM_v0: false`

Canonical public summaries:
- `README.md`
- `State_of_the_Theory.md`
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md`

Current validation commands:
- `pwsh -NoProfile -ExecutionPolicy Bypass -File ./governance_suite.ps1`
- `./py.ps1 -m pytest formal/python/tests -q`
- `Push-Location formal/toe_formal; lake build ToeFormal; Pop-Location`
- `git diff --exit-code`

Historical-only classes:
- `formal/tooling_snapshots`: retained historical snapshots, not live target authority.
- `scratch`: temporary workspace material unless explicitly promoted by a packet.
- `archive`: historical retained material unless explicitly cited by a current packet.
- `backup`: historical recovery material unless explicitly cited by a current packet.

Maintenance bindings:
- `REPOSITORY_ARTIFACT_RETENTION_POLICY_20260505_v0`
- `READ_ONLY_VALIDATION_HYGIENE_20260505_v0`
- `POST_READ_ONLY_VALIDATION_HYGIENE_BOUNDED_ATTACK_SELECTION_20260505_v0`
- `FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_AFTER_READ_ONLY_HYGIENE_20260505_v0`
- `ARTIFACT_RETENTION_ENFORCEMENT_PLAN_20260505_v0`
- `ARTIFACT_RETENTION_ENFORCEMENT_PLAN_RESULT_REVIEW_20260505_v0`
- `POST_ARTIFACT_RETENTION_ENFORCEMENT_BOUNDED_ATTACK_SELECTION_20260505_v0`
- `STATUS_SURFACE_CANONICALIZATION_PLAN_20260505_v0`
- `STATUS_SURFACE_CANONICALIZATION_PLAN_RESULT_REVIEW_20260505_v0`
- `POST_STATUS_SURFACE_CANONICALIZATION_BOUNDED_ATTACK_SELECTION_20260505_v0`
- `STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PACKET_20260505_v0`
- `STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PACKET_RESULT_REVIEW_20260505_v0`
- `POST_STATUS_SURFACE_ENFORCEMENT_BOUNDED_ATTACK_SELECTION_20260505_v0`
- `TOE_ALLOW_TRACKED_OUTPUT_WRITES=1`

Non-claim boundary:
- This index is an authority-surface navigation aid only.
- It does not authorize master-action promotion, pillar completion, seam closure, Phase 2 readiness, empirical adequacy, canonical ToE status, or QFT-GR source-map closure.
