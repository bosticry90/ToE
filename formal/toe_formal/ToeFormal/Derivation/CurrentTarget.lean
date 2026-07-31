import ToeFormal.Derivation.ToeGravitationalActionFamilyEligibilityHandoffResult

/-
Thin current-target aggregate for tiered validation. The five scientific
attempts are closed; the bounded survey's mandatory exit is selected but has
not yet been executed.
-/

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  ToeGravitationalActionFamilyEligibilityHandoffResult.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeGravitationalActionFamilyEligibilityHandoffResult.resultId

def currentBoundedProgramId : String :=
  ToeGravitationalActionFamilyEligibilityHandoffResult.programId

def currentBoundedProgramState : String := "CLOSED"

def currentTargetPhase : String :=
  "MANDATORY_EXIT_SELECTED_NOT_EXECUTED"

def currentBoundedAttemptNumber : Nat :=
  ToeGravitationalActionFamilyEligibilityHandoffResult.attemptSequenceNumber

def lastClosedBoundedSemanticStage : String :=
  ToeGravitationalActionFamilyEligibilityHandoffResult.semanticStageId

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_records_mandatory_survey_exit :
    currentLiveTarget =
      "close_toe_native_gravitational_requirements_and_candidate_action_family_survey_v0_after_bounded_result_v0" := by
  rfl

theorem survey_stage_five_is_closed_without_action_principle_or_successor_authority :
    currentBoundedProgramState = "CLOSED" ∧
    currentTargetPhase = "MANDATORY_EXIT_SELECTED_NOT_EXECUTED" ∧
    currentBoundedAttemptNumber = 5 ∧
    lastClosedBoundedSemanticStage = "CANDIDATE_ACTION_FAMILY_ELIGIBILITY_HANDOFF" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    ToeGravitationalActionFamilyEligibilityHandoffResult.eligibleNativeActionFamilyCount = 0 ∧
    ToeGravitationalActionFamilyEligibilityHandoffResult.gravitationalActionsSelected = 0 ∧
    ToeGravitationalActionFamilyEligibilityHandoffResult.nativeGravitationalPrinciplesSelectedOrDerived = 0 ∧
    ToeGravitationalActionFamilyEligibilityHandoffResult.successorProgramsAuthorizedInstalledOrOpened = 0 ∧
    ToeGravitationalActionFamilyEligibilityHandoffResult.mandatoryExitSelected = true ∧
    ToeGravitationalActionFamilyEligibilityHandoffResult.mandatoryExitCompleted = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
