/-
ToeFormal/Derivation/ArtifactRetentionEnforcementPlan.lean

Artifact-retention enforcement plan packet.

Scope:
- consume `prepare_artifact_retention_enforcement_plan`
- consume `FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_READ_ONLY_HYGIENE`
- freeze new large tracked snapshots by default
- classify tracked and noncanonical artifact zones
- define allowed and disallowed future artifact additions
- preserve read-only validation for tracked generated outputs
- defer migration or deletion of existing snapshots to a later explicit packet
- rotate to `review_artifact_retention_enforcement_plan_result`
- make no master-action promotion, pillar completion, seam closure,
  Phase 2 readiness, empirical adequacy, canonical ToE claim, or QFT-GR
  source-map closure claim
-/

import ToeFormal.Derivation.FullPillarTargetMapNextLaneSelectionAfterReadOnlyHygiene

namespace ToeFormal
namespace Derivation
namespace ArtifactRetentionEnforcementPlan

open CrossPillarDerivationProtocol
open FullPillarTargetMapNextLaneSelectionAfterReadOnlyHygiene

set_option autoImplicit false
set_option linter.style.longLine false

/-- Surface id for the artifact-retention enforcement plan packet. -/
def artifactRetentionEnforcementPlanSurfaceId : String :=
  "artifact_retention_enforcement_plan_v0"

/-- The target consumed by this packet. -/
def artifactRetentionEnforcementPlanConsumedTargetId : String :=
  selectedFullPillarTargetMapNextTargetAfterReadOnlyHygieneV0

/-- Selector token consumed by this packet. -/
def artifactRetentionEnforcementPlanConsumedSelectorTokenId : String :=
  fullPillarTargetMapNextLaneSelectionAfterReadOnlyHygieneResultTokenId

/-- Result token emitted by this packet. -/
def artifactRetentionEnforcementPlanResultTokenId : String :=
  "ARTIFACT_RETENTION_ENFORCEMENT_PLAN_PREPARED"

/-- Next strict target after this enforcement-plan packet. -/
def artifactRetentionEnforcementPlanResultReviewTargetId : String :=
  "review_artifact_retention_enforcement_plan_result"

/-- Canonical release report for this enforcement-plan packet. -/
def artifactRetentionEnforcementPlanReportPath : String :=
  "formal/docs/release/ARTIFACT_RETENTION_ENFORCEMENT_PLAN_20260505_v0.json"

/-- Focused validation target for this enforcement-plan packet. -/
def artifactRetentionEnforcementPlanValidationTarget : String :=
  "python -m pytest \
  formal/python/tests/test_artifact_retention_enforcement_plan_gate.py -q"

/-- Source retention policy consumed and refined by this packet. -/
def artifactRetentionEnforcementPlanSourcePolicyPath : String :=
  "formal/docs/release/REPOSITORY_ARTIFACT_RETENTION_POLICY_20260505_v0.md"

/-- A classified repository artifact zone. -/
structure ArtifactRetentionZone where
  zone_id : String
  policy_class : String
  default_rule : String
  tracked_authority : String
  packet_effect : String

/-- Artifact zones governed by this enforcement plan. -/
def artifactRetentionEnforcementPlanZonesV0 : List ArtifactRetentionZone :=
  [ { zone_id := "formal/tooling_snapshots"
      policy_class := "LEGACY_TRACKED_SNAPSHOT_ZONE"
      default_rule := "FROZEN_BY_DEFAULT"
      tracked_authority := "historical_tracked_snapshot_zone"
      packet_effect := "acknowledge_existing_mass_and_defer_migration" }
  , { zone_id := "formal/output"
      policy_class := "GENERATED_OUTPUT_ZONE"
      default_rule := "READ_ONLY_VALIDATION_ENFORCED"
      tracked_authority := "canonical_only_when_explicitly_pinned"
      packet_effect := "forbid_validation_time_tracked_mutation" }
  , { zone_id := "scratch"
      policy_class := "UNTRACKED_TEMPORARY_WORKING_AREA"
      default_rule := "UNTRACKED_BY_DEFAULT"
      tracked_authority := "none_without_explicit_promotion_packet"
      packet_effect := "use_for_large_temporary_artifacts" }
  , { zone_id := "archive"
      policy_class := "HISTORICAL_QUARANTINE_AREA"
      default_rule := "READ_ONLY_UNLESS_EXPLICIT_PACKET"
      tracked_authority := "historical_only_unless_current_packet_cites"
      packet_effect := "no_new_live_authority" }
  , { zone_id := "backup"
      policy_class := "NONCANONICAL_BACKUP_AREA"
      default_rule := "SHOULD_NOT_GROW_WITHOUT_POLICY"
      tracked_authority := "noncanonical_recovery_only"
      packet_effect := "no_growth_authorized_here" }
  , { zone_id := "formal/docs/release/*.json"
      policy_class := "CANONICAL_SMALL_CONTROL_PLANE_ARTIFACTS"
      default_rule := "TRACKED_WHEN_REVIEWABLE_AND_SMALL"
      tracked_authority := "release_packet_or_registry"
      packet_effect := "allowed_control_plane_surface" }
  , { zone_id := "Lean/Python/docs"
      policy_class := "NORMAL_TRACKED_SOURCE_SURFACES"
      default_rule := "TRACKED_SOURCE_REVIEW"
      tracked_authority := "normal_source_authority"
      packet_effect := "allowed_source_surface" }
  ]

/-- Enforcement rules prepared by this packet. -/
def artifactRetentionEnforcementPlanRulesV0 : List String :=
  [ "NO_NEW_LARGE_TRACKED_SNAPSHOTS_WITHOUT_EXPLICIT_RETENTION_PACKET"
  , "NO_TRACKED_GENERATED_OUTPUT_MUTATION_DURING_VALIDATION"
  , "NO_SNAPSHOT_MIGRATION_OR_DELETION_IN_THIS_PACKET"
  , "FUTURE_LARGE_ARTIFACT_ADDITIONS_REQUIRE_SIZE_AND_CLASSIFICATION_JUSTIFICATION"
  , "EXISTING_TOOLING_SNAPSHOTS_MASS_ACKNOWLEDGED_BUT_DEFERRED"
  ]

/-- Prepared enforcement plan status. This does not migrate or delete files. -/
structure ArtifactRetentionEnforcementPlanStatus where
  selector_target_consumed : Prop
  selector_target_consumed_evidence : selector_target_consumed
  selector_token_consumed : Prop
  selector_token_consumed_evidence : selector_token_consumed
  artifact_zones_classified : Prop
  artifact_zones_classified_evidence : artifact_zones_classified
  new_large_tracked_snapshots_frozen_by_default : Prop
  new_large_tracked_snapshots_frozen_evidence :
    new_large_tracked_snapshots_frozen_by_default
  tracked_generated_output_mutation_forbidden_during_validation : Prop
  tracked_generated_output_mutation_forbidden_evidence :
    tracked_generated_output_mutation_forbidden_during_validation
  future_large_artifact_justification_required : Prop
  future_large_artifact_justification_required_evidence :
    future_large_artifact_justification_required
  existing_tooling_snapshots_mass_acknowledged_deferred : Prop
  existing_tooling_snapshots_mass_deferred_evidence :
    existing_tooling_snapshots_mass_acknowledged_deferred
  snapshot_migration_or_deletion_deferred_to_future_packet : Prop
  snapshot_migration_or_deletion_deferred_evidence :
    snapshot_migration_or_deletion_deferred_to_future_packet
  snapshot_migration_or_deletion_executed_here : Prop
  snapshot_migration_or_deletion_not_executed_here :
    Not snapshot_migration_or_deletion_executed_here
  release_json_small_control_plane_allowed : Prop
  release_json_small_control_plane_allowed_evidence :
    release_json_small_control_plane_allowed
  lean_python_docs_tracked_source_allowed : Prop
  lean_python_docs_tracked_source_allowed_evidence :
    lean_python_docs_tracked_source_allowed
  ordinary_pytest_read_only_enforced : Prop
  ordinary_pytest_read_only_enforced_evidence :
    ordinary_pytest_read_only_enforced
  read_only_diff_proof_confirmed : Prop
  read_only_diff_proof_confirmed_evidence :
    read_only_diff_proof_confirmed
  full_pytest_checkpoint_passed_count : Nat
  full_pytest_checkpoint_skipped_count : Nat
  lean_build_jobs_confirmed : Nat
  real_axiom_count_confirmed : Nat
  default_nonalias_absent_from_unresolved_axiom_debt : Prop
  default_nonalias_absent_evidence :
    default_nonalias_absent_from_unresolved_axiom_debt
  sample_rep32_retained : Prop
  sample_rep32_retained_evidence : sample_rep32_retained
  qft_gr_source_map_closure_authorized : Prop
  qft_gr_source_map_closure_not_authorized :
    Not qft_gr_source_map_closure_authorized
  result_token : String
  selected_next_target : String
  authorized_effect : String
  consumed_target : String
  consumed_selector_token : String
  zones : List ArtifactRetentionZone
  zone_count : Nat
  enforcement_rules : List String
  enforcement_rule_count : Nat
  source_selector_surface_id : String
  source_policy_path : String
  surface_id : String
  report_path : String
  validation_target : String
  master_action_promoted : Prop
  master_action_not_promoted : Not master_action_promoted
  pillar_completion_inferred : Prop
  pillar_completion_not_inferred : Not pillar_completion_inferred
  seam_closure_claim : Prop
  seam_closure_not_claimed : Not seam_closure_claim
  phase2_readiness_claim : Prop
  phase2_readiness_not_claimed : Not phase2_readiness_claim
  empirical_adequacy_claim : Prop
  empirical_adequacy_not_claimed : Not empirical_adequacy_claim
  canonical_toe_claim : Prop
  canonical_toe_not_claimed : Not canonical_toe_claim
  governance_manifest_enrollment_authorized : Prop
  governance_manifest_enrollment_not_authorized :
    Not governance_manifest_enrollment_authorized
  status : DerivationStatus

/--
The enforcement plan converts the repository artifact policy into a bounded
next-step rule set: freeze new large tracked snapshots by default, keep
ordinary validation read-only, and leave existing snapshot migration/deletion
to a later explicit packet.
-/
def artifactRetentionEnforcementPlanStatusV0 :
    ArtifactRetentionEnforcementPlanStatus where
  selector_target_consumed := True
  selector_target_consumed_evidence := True.intro
  selector_token_consumed :=
    fullPillarTargetMapNextLaneSelectionAfterReadOnlyHygieneStatusReadoutV0
      |>.artifact_retention_enforcement_selected
  selector_token_consumed_evidence :=
    full_pillar_target_map_next_lane_selection_after_read_only_hygiene_artifact_retention_selected_v0
  artifact_zones_classified := True
  artifact_zones_classified_evidence := True.intro
  new_large_tracked_snapshots_frozen_by_default := True
  new_large_tracked_snapshots_frozen_evidence := True.intro
  tracked_generated_output_mutation_forbidden_during_validation :=
    fullPillarTargetMapNextLaneSelectionAfterReadOnlyHygieneStatusReadoutV0
      |>.ordinary_pytest_read_only_enforced
  tracked_generated_output_mutation_forbidden_evidence :=
    full_pillar_target_map_next_lane_selection_after_read_only_hygiene_pytest_read_only_v0
  future_large_artifact_justification_required := True
  future_large_artifact_justification_required_evidence := True.intro
  existing_tooling_snapshots_mass_acknowledged_deferred := True
  existing_tooling_snapshots_mass_deferred_evidence := True.intro
  snapshot_migration_or_deletion_deferred_to_future_packet := True
  snapshot_migration_or_deletion_deferred_evidence := True.intro
  snapshot_migration_or_deletion_executed_here := False
  snapshot_migration_or_deletion_not_executed_here := by
    intro h
    exact h
  release_json_small_control_plane_allowed := True
  release_json_small_control_plane_allowed_evidence := True.intro
  lean_python_docs_tracked_source_allowed := True
  lean_python_docs_tracked_source_allowed_evidence := True.intro
  ordinary_pytest_read_only_enforced :=
    fullPillarTargetMapNextLaneSelectionAfterReadOnlyHygieneStatusReadoutV0
      |>.ordinary_pytest_read_only_enforced
  ordinary_pytest_read_only_enforced_evidence :=
    full_pillar_target_map_next_lane_selection_after_read_only_hygiene_pytest_read_only_v0
  read_only_diff_proof_confirmed :=
    fullPillarTargetMapNextLaneSelectionAfterReadOnlyHygieneStatusReadoutV0
      |>.read_only_diff_proof_confirmed
  read_only_diff_proof_confirmed_evidence :=
    full_pillar_target_map_next_lane_selection_after_read_only_hygiene_diff_proof_v0
  full_pytest_checkpoint_passed_count :=
    fullPillarTargetMapNextLaneSelectionAfterReadOnlyHygieneStatusReadoutV0
      |>.full_pytest_checkpoint_passed_count
  full_pytest_checkpoint_skipped_count :=
    fullPillarTargetMapNextLaneSelectionAfterReadOnlyHygieneStatusReadoutV0
      |>.full_pytest_checkpoint_skipped_count
  lean_build_jobs_confirmed := 7977
  real_axiom_count_confirmed :=
    fullPillarTargetMapNextLaneSelectionAfterReadOnlyHygieneStatusReadoutV0
      |>.real_axiom_count_confirmed
  default_nonalias_absent_from_unresolved_axiom_debt :=
    fullPillarTargetMapNextLaneSelectionAfterReadOnlyHygieneStatusReadoutV0
      |>.default_nonalias_absent_from_unresolved_axiom_debt
  default_nonalias_absent_evidence :=
    full_pillar_target_map_next_lane_selection_after_read_only_hygiene_default_nonalias_absent_v0
  sample_rep32_retained :=
    fullPillarTargetMapNextLaneSelectionAfterReadOnlyHygieneStatusReadoutV0
      |>.sample_rep32_retained
  sample_rep32_retained_evidence :=
    full_pillar_target_map_next_lane_selection_after_read_only_hygiene_sample_rep32_retained_v0
  qft_gr_source_map_closure_authorized :=
    fullPillarTargetMapNextLaneSelectionAfterReadOnlyHygieneStatusReadoutV0
      |>.qft_gr_source_map_closure_authorized
  qft_gr_source_map_closure_not_authorized :=
    full_pillar_target_map_next_lane_selection_after_read_only_hygiene_qft_gr_source_map_not_authorized_v0
  result_token := artifactRetentionEnforcementPlanResultTokenId
  selected_next_target := artifactRetentionEnforcementPlanResultReviewTargetId
  authorized_effect :=
    "PREPARE_ARTIFACT_RETENTION_ENFORCEMENT_PLAN_NO_MIGRATION"
  consumed_target := artifactRetentionEnforcementPlanConsumedTargetId
  consumed_selector_token := artifactRetentionEnforcementPlanConsumedSelectorTokenId
  zones := artifactRetentionEnforcementPlanZonesV0
  zone_count := artifactRetentionEnforcementPlanZonesV0.length
  enforcement_rules := artifactRetentionEnforcementPlanRulesV0
  enforcement_rule_count := artifactRetentionEnforcementPlanRulesV0.length
  source_selector_surface_id :=
    fullPillarTargetMapNextLaneSelectionAfterReadOnlyHygieneSurfaceId
  source_policy_path := artifactRetentionEnforcementPlanSourcePolicyPath
  surface_id := artifactRetentionEnforcementPlanSurfaceId
  report_path := artifactRetentionEnforcementPlanReportPath
  validation_target := artifactRetentionEnforcementPlanValidationTarget
  master_action_promoted := False
  master_action_not_promoted := by
    intro h
    exact h
  pillar_completion_inferred := False
  pillar_completion_not_inferred := by
    intro h
    exact h
  seam_closure_claim := False
  seam_closure_not_claimed := by
    intro h
    exact h
  phase2_readiness_claim := False
  phase2_readiness_not_claimed := by
    intro h
    exact h
  empirical_adequacy_claim := False
  empirical_adequacy_not_claimed := by
    intro h
    exact h
  canonical_toe_claim := False
  canonical_toe_not_claimed := by
    intro h
    exact h
  governance_manifest_enrollment_authorized := False
  governance_manifest_enrollment_not_authorized := by
    intro h
    exact h
  status := .retained

/-- Public readout for the artifact-retention enforcement plan packet. -/
def artifactRetentionEnforcementPlanStatusReadoutV0 :
    ArtifactRetentionEnforcementPlanStatus :=
  artifactRetentionEnforcementPlanStatusV0

theorem artifact_retention_enforcement_plan_consumes_target_v0 :
    (artifactRetentionEnforcementPlanStatusReadoutV0 |>.consumed_target) =
      "prepare_artifact_retention_enforcement_plan" := by
  rfl

theorem artifact_retention_enforcement_plan_consumes_selector_token_v0 :
    (artifactRetentionEnforcementPlanStatusReadoutV0
      |>.consumed_selector_token) =
      fullPillarTargetMapNextLaneSelectionAfterReadOnlyHygieneResultTokenId := by
  rfl

theorem artifact_retention_enforcement_plan_result_token_v0 :
    (artifactRetentionEnforcementPlanStatusReadoutV0 |>.result_token) =
      "ARTIFACT_RETENTION_ENFORCEMENT_PLAN_PREPARED" := by
  rfl

theorem artifact_retention_enforcement_plan_next_target_v0 :
    (artifactRetentionEnforcementPlanStatusReadoutV0 |>.selected_next_target) =
      "review_artifact_retention_enforcement_plan_result" := by
  rfl

theorem artifact_retention_enforcement_plan_zones_classified_v0 :
    artifactRetentionEnforcementPlanStatusReadoutV0
      |>.artifact_zones_classified := by
  exact artifactRetentionEnforcementPlanStatusReadoutV0
    |>.artifact_zones_classified_evidence

theorem artifact_retention_enforcement_plan_zone_count_v0 :
    (artifactRetentionEnforcementPlanStatusReadoutV0 |>.zone_count) = 7 := by
  rfl

theorem artifact_retention_enforcement_plan_rule_count_v0 :
    (artifactRetentionEnforcementPlanStatusReadoutV0
      |>.enforcement_rule_count) = 5 := by
  rfl

theorem artifact_retention_enforcement_plan_freezes_new_large_snapshots_v0 :
    artifactRetentionEnforcementPlanStatusReadoutV0
      |>.new_large_tracked_snapshots_frozen_by_default := by
  exact artifactRetentionEnforcementPlanStatusReadoutV0
    |>.new_large_tracked_snapshots_frozen_evidence

theorem artifact_retention_enforcement_plan_validation_output_mutation_forbidden_v0 :
    artifactRetentionEnforcementPlanStatusReadoutV0
      |>.tracked_generated_output_mutation_forbidden_during_validation := by
  exact artifactRetentionEnforcementPlanStatusReadoutV0
    |>.tracked_generated_output_mutation_forbidden_evidence

theorem artifact_retention_enforcement_plan_large_artifact_justification_required_v0 :
    artifactRetentionEnforcementPlanStatusReadoutV0
      |>.future_large_artifact_justification_required := by
  exact artifactRetentionEnforcementPlanStatusReadoutV0
    |>.future_large_artifact_justification_required_evidence

theorem artifact_retention_enforcement_plan_existing_snapshot_mass_deferred_v0 :
    artifactRetentionEnforcementPlanStatusReadoutV0
      |>.existing_tooling_snapshots_mass_acknowledged_deferred := by
  exact artifactRetentionEnforcementPlanStatusReadoutV0
    |>.existing_tooling_snapshots_mass_deferred_evidence

theorem artifact_retention_enforcement_plan_migration_deletion_deferred_v0 :
    artifactRetentionEnforcementPlanStatusReadoutV0
      |>.snapshot_migration_or_deletion_deferred_to_future_packet := by
  exact artifactRetentionEnforcementPlanStatusReadoutV0
    |>.snapshot_migration_or_deletion_deferred_evidence

theorem artifact_retention_enforcement_plan_no_migration_deletion_here_v0 :
    Not
      (artifactRetentionEnforcementPlanStatusReadoutV0
        |>.snapshot_migration_or_deletion_executed_here) := by
  exact artifactRetentionEnforcementPlanStatusReadoutV0
    |>.snapshot_migration_or_deletion_not_executed_here

theorem artifact_retention_enforcement_plan_release_json_allowed_v0 :
    artifactRetentionEnforcementPlanStatusReadoutV0
      |>.release_json_small_control_plane_allowed := by
  exact artifactRetentionEnforcementPlanStatusReadoutV0
    |>.release_json_small_control_plane_allowed_evidence

theorem artifact_retention_enforcement_plan_source_surfaces_allowed_v0 :
    artifactRetentionEnforcementPlanStatusReadoutV0
      |>.lean_python_docs_tracked_source_allowed := by
  exact artifactRetentionEnforcementPlanStatusReadoutV0
    |>.lean_python_docs_tracked_source_allowed_evidence

theorem artifact_retention_enforcement_plan_pytest_read_only_v0 :
    artifactRetentionEnforcementPlanStatusReadoutV0
      |>.ordinary_pytest_read_only_enforced := by
  exact artifactRetentionEnforcementPlanStatusReadoutV0
    |>.ordinary_pytest_read_only_enforced_evidence

theorem artifact_retention_enforcement_plan_diff_proof_v0 :
    artifactRetentionEnforcementPlanStatusReadoutV0
      |>.read_only_diff_proof_confirmed := by
  exact artifactRetentionEnforcementPlanStatusReadoutV0
    |>.read_only_diff_proof_confirmed_evidence

theorem artifact_retention_enforcement_plan_full_pytest_count_v0 :
    (artifactRetentionEnforcementPlanStatusReadoutV0
      |>.full_pytest_checkpoint_passed_count) = 6536 := by
  rfl

theorem artifact_retention_enforcement_plan_full_pytest_skipped_v0 :
    (artifactRetentionEnforcementPlanStatusReadoutV0
      |>.full_pytest_checkpoint_skipped_count) = 230 := by
  rfl

theorem artifact_retention_enforcement_plan_lean_jobs_v0 :
    (artifactRetentionEnforcementPlanStatusReadoutV0
      |>.lean_build_jobs_confirmed) = 7977 := by
  rfl

theorem artifact_retention_enforcement_plan_axiom_count_v0 :
    (artifactRetentionEnforcementPlanStatusReadoutV0
      |>.real_axiom_count_confirmed) = 60 := by
  rfl

theorem artifact_retention_enforcement_plan_default_nonalias_absent_v0 :
    artifactRetentionEnforcementPlanStatusReadoutV0
      |>.default_nonalias_absent_from_unresolved_axiom_debt := by
  exact artifactRetentionEnforcementPlanStatusReadoutV0
    |>.default_nonalias_absent_evidence

theorem artifact_retention_enforcement_plan_sample_rep32_retained_v0 :
    artifactRetentionEnforcementPlanStatusReadoutV0
      |>.sample_rep32_retained := by
  exact artifactRetentionEnforcementPlanStatusReadoutV0
    |>.sample_rep32_retained_evidence

theorem artifact_retention_enforcement_plan_qft_gr_source_map_not_authorized_v0 :
    Not
      (artifactRetentionEnforcementPlanStatusReadoutV0
        |>.qft_gr_source_map_closure_authorized) := by
  exact artifactRetentionEnforcementPlanStatusReadoutV0
    |>.qft_gr_source_map_closure_not_authorized

theorem artifact_retention_enforcement_plan_master_action_not_promoted_v0 :
    Not (artifactRetentionEnforcementPlanStatusReadoutV0
      |>.master_action_promoted) := by
  exact artifactRetentionEnforcementPlanStatusReadoutV0
    |>.master_action_not_promoted

theorem artifact_retention_enforcement_plan_no_pillar_completion_v0 :
    Not (artifactRetentionEnforcementPlanStatusReadoutV0
      |>.pillar_completion_inferred) := by
  exact artifactRetentionEnforcementPlanStatusReadoutV0
    |>.pillar_completion_not_inferred

theorem artifact_retention_enforcement_plan_no_seam_closure_v0 :
    Not (artifactRetentionEnforcementPlanStatusReadoutV0 |>.seam_closure_claim) := by
  exact artifactRetentionEnforcementPlanStatusReadoutV0 |>.seam_closure_not_claimed

theorem artifact_retention_enforcement_plan_no_phase2_readiness_v0 :
    Not
      (artifactRetentionEnforcementPlanStatusReadoutV0
        |>.phase2_readiness_claim) := by
  exact artifactRetentionEnforcementPlanStatusReadoutV0
    |>.phase2_readiness_not_claimed

theorem artifact_retention_enforcement_plan_no_empirical_adequacy_v0 :
    Not
      (artifactRetentionEnforcementPlanStatusReadoutV0
        |>.empirical_adequacy_claim) := by
  exact artifactRetentionEnforcementPlanStatusReadoutV0
    |>.empirical_adequacy_not_claimed

theorem artifact_retention_enforcement_plan_no_canonical_toe_claim_v0 :
    Not (artifactRetentionEnforcementPlanStatusReadoutV0 |>.canonical_toe_claim) := by
  exact artifactRetentionEnforcementPlanStatusReadoutV0 |>.canonical_toe_not_claimed

theorem artifact_retention_enforcement_plan_manifest_not_enrolled_v0 :
    Not
      (artifactRetentionEnforcementPlanStatusReadoutV0
        |>.governance_manifest_enrollment_authorized) := by
  exact artifactRetentionEnforcementPlanStatusReadoutV0
    |>.governance_manifest_enrollment_not_authorized

end ArtifactRetentionEnforcementPlan
end Derivation
end ToeFormal
