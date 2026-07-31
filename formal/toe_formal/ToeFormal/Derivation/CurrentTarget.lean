import ToeFormal.Derivation.ToeNativeGravitationalRequirementInventoryResult

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
  ToeNativeGravitationalRequirementInventoryResult.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeGravitationalRequirementInventoryResult.reviewId

def currentBoundedProgramId : String :=
  ToeNativeGravitationalRequirementInventoryResult.programId

def currentBoundedProgramState : String := "CLOSED"

def currentTargetPhase : String :=
  "STAGE_1_CLOSED_PASSED_AWAITING_SEPARATE_STAGE_2_AUTHORITY"

def currentBoundedAttemptNumber : Nat :=
  ToeNativeGravitationalRequirementInventoryResult.attemptSequenceNumber

def lastClosedBoundedSemanticStage : String :=
  "NATIVE_GRAVITATIONAL_REQUIREMENT_INVENTORY"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_selects_unopened_candidate_action_family_inventory :
    currentLiveTarget =
      "inventory_toe_candidate_gravitational_action_families_v0" := by
  rfl

theorem gravitational_requirement_inventory_is_closed_passed_with_conflicts :
    currentBoundedProgramId =
      "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0" ∧
    currentBoundedProgramState = "CLOSED" ∧
    currentTargetPhase =
      "STAGE_1_CLOSED_PASSED_AWAITING_SEPARATE_STAGE_2_AUTHORITY" ∧
    currentBoundedAttemptNumber = 1 ∧
    lastClosedBoundedSemanticStage =
      "NATIVE_GRAVITATIONAL_REQUIREMENT_INVENTORY" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    ToeNativeGravitationalRequirementInventoryResult.requirementInventoryComplete =
      true ∧
    ToeNativeGravitationalRequirementInventoryResult.conflictsPreserved = true ∧
    ToeNativeGravitationalRequirementInventoryResult.actionFamiliesCompared =
      false ∧
    ToeNativeGravitationalRequirementInventoryResult.gravitationalActionSelected =
      false ∧
    ToeNativeGravitationalRequirementInventoryResult.stageTwoAuthorized = false ∧
    ToeNativeGravitationalRequirementInventoryResult.stageTwoOpened = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
