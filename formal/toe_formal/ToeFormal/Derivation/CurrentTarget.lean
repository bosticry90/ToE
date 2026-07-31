import ToeFormal.Derivation.ToeGravitationalActionFamilyEligibilityHandoffAttemptOpen

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
  ToeGravitationalActionFamilyEligibilityHandoffAttemptOpen.scientificTarget

def currentEvidencePacketId : String :=
  ToeGravitationalActionFamilyEligibilityHandoffAttemptOpen.eventId

def currentBoundedProgramId : String :=
  ToeGravitationalActionFamilyEligibilityHandoffAttemptOpen.programId

def currentBoundedProgramState : String := "OPEN"

def currentTargetPhase : String :=
  "STAGE_5_SCIENTIFIC_ATTEMPT_OPEN"

def currentBoundedAttemptNumber : Nat :=
  ToeGravitationalActionFamilyEligibilityHandoffAttemptOpen.attemptSequenceNumber

def lastClosedBoundedSemanticStage : String :=
  "SOURCE_BOUND_REQUIREMENT_FAMILY_COMPATIBILITY_SURVEY"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_records_open_eligibility_handoff :
    currentLiveTarget =
      "select_toe_gravitational_action_family_eligibility_handoff_v0" := by
  rfl

theorem gravitational_action_family_eligibility_handoff_is_open_without_result :
    currentBoundedProgramId =
      "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0" ∧
    currentBoundedProgramState = "OPEN" ∧
    currentTargetPhase =
      "STAGE_5_SCIENTIFIC_ATTEMPT_OPEN" ∧
    currentBoundedAttemptNumber = 5 ∧
    lastClosedBoundedSemanticStage =
      "SOURCE_BOUND_REQUIREMENT_FAMILY_COMPATIBILITY_SURVEY" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    ToeGravitationalActionFamilyEligibilityHandoffAttemptOpen.programOpen = true ∧
    ToeGravitationalActionFamilyEligibilityHandoffAttemptOpen.scientificResultCreated = false ∧
    ToeGravitationalActionFamilyEligibilityHandoffAttemptOpen.eligibilityClassificationsMade = 0 ∧
    ToeGravitationalActionFamilyEligibilityHandoffAttemptOpen.routesSelected = 0 ∧
    ToeGravitationalActionFamilyEligibilityHandoffAttemptOpen.gravitationalActionsSelected = 0 ∧
    ToeGravitationalActionFamilyEligibilityHandoffAttemptOpen.nativeGravitationalPrinciplesSelected = 0 ∧
    ToeGravitationalActionFamilyEligibilityHandoffAttemptOpen.successorProgramsAuthorized = 0 ∧
    ToeGravitationalActionFamilyEligibilityHandoffAttemptOpen.evidencePromoted = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
