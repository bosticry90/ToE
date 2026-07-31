import ToeFormal.Derivation.ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyAttemptOpen

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
  ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyAttemptOpen.scientificTarget

def currentEvidencePacketId : String :=
  ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyAttemptOpen.eventId

def currentBoundedProgramId : String :=
  ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyAttemptOpen.programId

def currentBoundedProgramState : String := "OPEN"

def currentTargetPhase : String :=
  "STAGE_4_SCIENTIFIC_ATTEMPT_OPEN"

def currentBoundedAttemptNumber : Nat :=
  ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyAttemptOpen.attemptSequenceNumber

def lastClosedBoundedSemanticStage : String :=
  "GRAVITATIONAL_REQUIREMENT_AND_FAMILY_LINEAGE_RECONSTRUCTION"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_records_open_requirement_family_compatibility_survey :
    currentLiveTarget =
      "survey_toe_source_bound_gravitational_requirement_family_compatibility_v0" := by
  rfl

theorem source_bound_requirement_family_compatibility_survey_is_open_without_result :
    currentBoundedProgramId =
      "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0" ∧
    currentBoundedProgramState = "OPEN" ∧
    currentTargetPhase =
      "STAGE_4_SCIENTIFIC_ATTEMPT_OPEN" ∧
    currentBoundedAttemptNumber = 4 ∧
    lastClosedBoundedSemanticStage =
      "GRAVITATIONAL_REQUIREMENT_AND_FAMILY_LINEAGE_RECONSTRUCTION" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyAttemptOpen.programOpen = true ∧
    ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyAttemptOpen.scientificResultCreated = false ∧
    ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyAttemptOpen.compatibilityCellsPopulated = 0 ∧
    ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyAttemptOpen.familiesEligibleForNativeSelection = 0 ∧
    ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyAttemptOpen.evidencePromoted = false ∧
    ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyAttemptOpen.gravitationalActionSelected = false ∧
    ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyAttemptOpen.stageFiveAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
