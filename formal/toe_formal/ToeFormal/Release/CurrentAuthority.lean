import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationV0
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationResultReviewV0

/-
Release-facing current-authority aggregate for tiered validation. It is a small
build target for authority-surface synchronization checks and intentionally
does not replace the full ToeFormal release aggregate.
-/

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"

def currentTarget : String :=
  Derivation.CurrentTarget.currentLiveTarget

def currentEvidencePacketId : String :=
  Derivation.CurrentTarget.currentEvidencePacketId

def boundedProgramId : String :=
  Derivation.CurrentTarget.currentBoundedProgramId

def boundedProgramState : String :=
  Derivation.CurrentTarget.currentBoundedProgramState

def currentTargetPhase : String :=
  Derivation.CurrentTarget.currentTargetPhase

def boundedAttemptNumber : Nat :=
  Derivation.CurrentTarget.currentBoundedAttemptNumber

theorem current_authority_tracks_selected_unopened_requirement_family_compatibility_survey :
    currentTarget =
      "survey_toe_source_bound_gravitational_requirement_family_compatibility_v0" := by
  native_decide

theorem bounded_program_governance_installation_preserved_its_then_current_target :
    BoundedProgramGovernanceControlInstallationV0.scientificTarget =
      "prepare_qft_gr_quadratic_generic_background_linearization_gauge_and_jet_contract_v0" ∧
    BoundedProgramGovernanceControlInstallationV0.scientificTargetRotated =
      false := by
  native_decide

theorem bounded_program_governance_review_preserved_its_then_current_target :
    BoundedProgramGovernanceControlInstallationResultReviewV0.scientificTarget =
      "prepare_qft_gr_quadratic_generic_background_linearization_gauge_and_jet_contract_v0" := by
  native_decide

theorem gravitational_lineage_reconstruction_stage_is_closed_passed :
    boundedProgramId =
      "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0" ∧
    boundedProgramState = "CLOSED" ∧
    currentTargetPhase =
      "STAGE_3_CLOSED_PASSED_AWAITING_SEPARATE_STAGE_4_AUTHORITY" ∧
    boundedAttemptNumber = 3 ∧
    Derivation.ToeGravitationalRequirementAndActionFamilyLineageReconstructionResult.lineagesReconstructed =
      true ∧
    Derivation.ToeGravitationalRequirementAndActionFamilyLineageReconstructionResult.boundedUnresolvedRelationshipsPreserved =
      true ∧
    Derivation.ToeGravitationalRequirementAndActionFamilyLineageReconstructionResult.definedNativeActionFamilyCount =
      0 ∧
    Derivation.ToeGravitationalRequirementAndActionFamilyLineageReconstructionResult.compatibilityJudgmentsMade =
      false ∧
    Derivation.ToeGravitationalRequirementAndActionFamilyLineageReconstructionResult.gravitationalActionSelected =
      false ∧
    Derivation.ToeGravitationalRequirementAndActionFamilyLineageReconstructionResult.stageFourAuthorized =
      false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
