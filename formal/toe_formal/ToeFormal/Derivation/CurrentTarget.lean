import ToeFormal.Derivation.ToeCandidateGravitationalActionFamilyInventoryResult

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
  ToeCandidateGravitationalActionFamilyInventoryResult.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeCandidateGravitationalActionFamilyInventoryResult.reviewId

def currentBoundedProgramId : String :=
  ToeCandidateGravitationalActionFamilyInventoryResult.programId

def currentBoundedProgramState : String := "CLOSED"

def currentTargetPhase : String :=
  "STAGE_2_CLOSED_PASSED_AWAITING_SEPARATE_STAGE_3_AUTHORITY"

def currentBoundedAttemptNumber : Nat :=
  ToeCandidateGravitationalActionFamilyInventoryResult.attemptSequenceNumber

def lastClosedBoundedSemanticStage : String :=
  "CANDIDATE_GRAVITATIONAL_ACTION_FAMILY_INVENTORY"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_selects_unopened_gravitational_lineage_reconstruction :
    currentLiveTarget =
      "reconstruct_toe_gravitational_requirement_and_action_family_lineages_v0" := by
  rfl

theorem candidate_action_family_inventory_is_closed_passed_with_unresolved_meanings :
    currentBoundedProgramId =
      "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0" ∧
    currentBoundedProgramState = "CLOSED" ∧
    currentTargetPhase =
      "STAGE_2_CLOSED_PASSED_AWAITING_SEPARATE_STAGE_3_AUTHORITY" ∧
    currentBoundedAttemptNumber = 2 ∧
    lastClosedBoundedSemanticStage =
      "CANDIDATE_GRAVITATIONAL_ACTION_FAMILY_INVENTORY" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    ToeCandidateGravitationalActionFamilyInventoryResult.inventoryComplete = true ∧
    ToeCandidateGravitationalActionFamilyInventoryResult.unresolvedMeaningsPreserved = true ∧
    ToeCandidateGravitationalActionFamilyInventoryResult.familiesRankedOrScored = false ∧
    ToeCandidateGravitationalActionFamilyInventoryResult.requirementCompatibilityJudgmentsMade = false ∧
    ToeCandidateGravitationalActionFamilyInventoryResult.gravitationalActionSelected = false ∧
    ToeCandidateGravitationalActionFamilyInventoryResult.stageThreeAuthorized = false ∧
    ToeCandidateGravitationalActionFamilyInventoryResult.stageThreeOpened = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
