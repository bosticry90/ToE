namespace ToeFormal
namespace Release
namespace ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyProgramGovernanceInstallationV0

def programId : String :=
  "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0"

def preservedScientificTarget : String :=
  "prepare_toe_native_gravitational_requirements_and_candidate_action_family_survey_bounded_program_v0"

def mandatoryExitTarget : String :=
  "close_toe_native_gravitational_requirements_and_candidate_action_family_survey_v0_after_bounded_result_v0"

def authorizedStageCount : Nat := 5
def attemptedStageCount : Nat := 0
def repairAttemptCount : Nat := 0
def nativeRequirementCount : Nat := 10
def candidateActionFamilyCount : Nat := 7
def compatibilityCellCeiling : Nat := 70
def programInstalled : Bool := true
def programOpened : Bool := false
def scientificTargetRotated : Bool := false
def scientificOutputCreated : Bool := false
def compatibilitySurveyExecuted : Bool := false
def evidencePromoted : Bool := false
def gravitationalActionSelected : Bool := false
def nativeGravitationalPrincipleSelected : Bool := false
def gravitationalCalculationStarted : Bool := false

theorem governance_installation_is_bounded_unopened_and_nonselecting :
    programInstalled = true ∧
    programOpened = false ∧
    authorizedStageCount = 5 ∧
    attemptedStageCount = 0 ∧
    repairAttemptCount = 0 ∧
    nativeRequirementCount = 10 ∧
    candidateActionFamilyCount = 7 ∧
    compatibilityCellCeiling = 70 ∧
    scientificTargetRotated = false ∧
    scientificOutputCreated = false ∧
    compatibilitySurveyExecuted = false ∧
    evidencePromoted = false ∧
    gravitationalActionSelected = false ∧
    nativeGravitationalPrincipleSelected = false ∧
    gravitationalCalculationStarted = false := by
  decide

end ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyProgramGovernanceInstallationV0
end Release
end ToeFormal
