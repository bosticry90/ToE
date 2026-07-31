import ToeFormal.Derivation.ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyV0BoundedCloseout

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyV0BoundedCloseout

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := executionTarget
def currentEvidencePacketId : String := resultId
def currentBoundedProgramId : String := programId
def currentBoundedProgramState : String := "TERMINAL"
def currentTargetPhase : String := "PROGRAM_CLOSED_AFTER_MANDATORY_EXIT"
def currentBoundedAttemptNumber : Nat := 5
def lastClosedBoundedSemanticStage : String := "CANDIDATE_ACTION_FAMILY_ELIGIBILITY_HANDOFF"
def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_records_completed_gravitational_survey_mandatory_exit :
    currentLiveTarget =
      "close_toe_native_gravitational_requirements_and_candidate_action_family_survey_v0_after_bounded_result_v0" := by
  rfl

theorem gravitational_survey_is_terminal_without_principle_action_or_successor_authority :
    currentBoundedProgramState = "TERMINAL" ∧
    currentTargetPhase = "PROGRAM_CLOSED_AFTER_MANDATORY_EXIT" ∧
    currentBoundedAttemptNumber = 5 ∧
    lastClosedBoundedSemanticStage = "CANDIDATE_ACTION_FAMILY_ELIGIBILITY_HANDOFF" ∧
    mandatoryExitCompleted = true ∧
    eligibleNativeActionFamilyCount = 0 ∧
    positiveNativeGravitationalPrincipleSelectedOrDerived = false ∧
    nativeGravitationalActionSelectedOrAdopted = false ∧
    successorProgramAuthorized = false ∧ successorProgramInstalled = false ∧
    successorProgramOpened = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
