import ToeFormal.Derivation.ToeCandidateGravitationalActionFamilyInventoryAttemptOpen

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
  ToeCandidateGravitationalActionFamilyInventoryAttemptOpen.scientificTarget

def currentEvidencePacketId : String :=
  ToeCandidateGravitationalActionFamilyInventoryAttemptOpen.eventId

def currentBoundedProgramId : String :=
  ToeCandidateGravitationalActionFamilyInventoryAttemptOpen.programId

def currentBoundedProgramState : String := "OPEN"

def currentTargetPhase : String :=
  "STAGE_2_SCIENTIFIC_ATTEMPT_OPEN"

def currentBoundedAttemptNumber : Nat :=
  ToeCandidateGravitationalActionFamilyInventoryAttemptOpen.attemptSequenceNumber

def lastClosedBoundedSemanticStage : String :=
  "NATIVE_GRAVITATIONAL_REQUIREMENT_INVENTORY"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_records_open_candidate_action_family_inventory :
    currentLiveTarget =
      "inventory_toe_candidate_gravitational_action_families_v0" := by
  rfl

theorem candidate_action_family_inventory_is_open_without_result :
    currentBoundedProgramId =
      "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0" ∧
    currentBoundedProgramState = "OPEN" ∧
    currentTargetPhase =
      "STAGE_2_SCIENTIFIC_ATTEMPT_OPEN" ∧
    currentBoundedAttemptNumber = 2 ∧
    lastClosedBoundedSemanticStage =
      "NATIVE_GRAVITATIONAL_REQUIREMENT_INVENTORY" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    ToeCandidateGravitationalActionFamilyInventoryAttemptOpen.programOpen = true ∧
    ToeCandidateGravitationalActionFamilyInventoryAttemptOpen.scientificResultCreated = false ∧
    ToeCandidateGravitationalActionFamilyInventoryAttemptOpen.actionFamiliesInventoried = 0 ∧
    ToeCandidateGravitationalActionFamilyInventoryAttemptOpen.actionFamiliesCompared = false ∧
    ToeCandidateGravitationalActionFamilyInventoryAttemptOpen.gravitationalActionSelected = false ∧
    ToeCandidateGravitationalActionFamilyInventoryAttemptOpen.stageThreeAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
