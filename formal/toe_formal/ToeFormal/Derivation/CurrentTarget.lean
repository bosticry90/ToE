import ToeFormal.Derivation.ToeGravitationalRequirementAndActionFamilyLineageReconstructionResult

/-
Thin current-target aggregate for tiered validation. This target follows the
live strict target and avoids requiring a full ToeFormal aggregate build for
routine packet checks.
-/

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  ToeGravitationalRequirementAndActionFamilyLineageReconstructionResult.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeGravitationalRequirementAndActionFamilyLineageReconstructionResult.reviewId

def currentBoundedProgramId : String :=
  ToeGravitationalRequirementAndActionFamilyLineageReconstructionResult.programId

def currentBoundedProgramState : String := "CLOSED"

def currentTargetPhase : String :=
  "STAGE_3_CLOSED_PASSED_AWAITING_SEPARATE_STAGE_4_AUTHORITY"

def currentBoundedAttemptNumber : Nat :=
  ToeGravitationalRequirementAndActionFamilyLineageReconstructionResult.attemptSequenceNumber

def lastClosedBoundedSemanticStage : String :=
  "GRAVITATIONAL_REQUIREMENT_AND_FAMILY_LINEAGE_RECONSTRUCTION"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_selects_unopened_requirement_family_compatibility_survey :
    currentLiveTarget =
      "survey_toe_source_bound_gravitational_requirement_family_compatibility_v0" := by
  rfl

theorem gravitational_lineage_reconstruction_is_closed_passed_with_unresolved_relationships :
    currentBoundedProgramId =
      "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0" ∧
    currentBoundedProgramState = "CLOSED" ∧
    currentTargetPhase =
      "STAGE_3_CLOSED_PASSED_AWAITING_SEPARATE_STAGE_4_AUTHORITY" ∧
    currentBoundedAttemptNumber = 3 ∧
    lastClosedBoundedSemanticStage =
      "GRAVITATIONAL_REQUIREMENT_AND_FAMILY_LINEAGE_RECONSTRUCTION" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    ToeGravitationalRequirementAndActionFamilyLineageReconstructionResult.lineagesReconstructed = true ∧
    ToeGravitationalRequirementAndActionFamilyLineageReconstructionResult.boundedUnresolvedRelationshipsPreserved = true ∧
    ToeGravitationalRequirementAndActionFamilyLineageReconstructionResult.definedNativeActionFamilyCount = 0 ∧
    ToeGravitationalRequirementAndActionFamilyLineageReconstructionResult.compatibilityJudgmentsMade = false ∧
    ToeGravitationalRequirementAndActionFamilyLineageReconstructionResult.gravitationalActionSelected = false ∧
    ToeGravitationalRequirementAndActionFamilyLineageReconstructionResult.stageFourAuthorized = false ∧
    ToeGravitationalRequirementAndActionFamilyLineageReconstructionResult.stageFourOpened = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
