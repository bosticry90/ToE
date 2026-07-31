import ToeFormal.Derivation.ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyResult

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
  ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyResult.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyResult.resultId

def currentBoundedProgramId : String :=
  ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyResult.programId

def currentBoundedProgramState : String := "CLOSED"

def currentTargetPhase : String :=
  "STAGE_5_SELECTED_UNOPENED_AFTER_STAGE_4_PASS"

def currentBoundedAttemptNumber : Nat :=
  ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyResult.attemptSequenceNumber

def lastClosedBoundedSemanticStage : String :=
  "SOURCE_BOUND_REQUIREMENT_FAMILY_COMPATIBILITY_SURVEY"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_records_selected_unopened_eligibility_handoff :
    currentLiveTarget =
      "select_toe_gravitational_action_family_eligibility_handoff_v0" := by
  rfl

theorem source_bound_requirement_family_compatibility_survey_closed_without_selection :
    currentBoundedProgramId =
      "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0" ∧
    currentBoundedProgramState = "CLOSED" ∧
    currentTargetPhase =
      "STAGE_5_SELECTED_UNOPENED_AFTER_STAGE_4_PASS" ∧
    currentBoundedAttemptNumber = 4 ∧
    lastClosedBoundedSemanticStage =
      "SOURCE_BOUND_REQUIREMENT_FAMILY_COMPATIBILITY_SURVEY" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyResult.compatibilityCellCount = 70 ∧
    ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyResult.observedDefinedNativeActionFamilyCount = 0 ∧
    ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyResult.gravitationalActionsSelected = 0 ∧
    ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyResult.nativeGravitationalPrinciplesDerivedOrPostulated = 0 ∧
    ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyResult.newGravitationalCalculationsExecuted = 0 ∧
    ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyResult.stageFiveEligibilityVerdictMade = false ∧
    ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyResult.stageFiveAuthorized = false ∧
    ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyResult.stageFiveOpened = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
