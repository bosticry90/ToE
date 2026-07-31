namespace ToeFormal
namespace Derivation
namespace ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyPreparationAuthorityV0

def authorityId : String :=
  "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_PREPARATION_AUTHORITY_v0"

def authorizedTarget : String :=
  "prepare_toe_native_gravitational_requirements_and_candidate_action_family_survey_bounded_program_v0"

def selectedFrontier : String :=
  "HYP_TOE_NATIVE_GRAVITATIONAL_PRINCIPLE_ACTION_SELECTION_v0"

def proposalPreparationAuthorized : Bool := true
def programInstalled : Bool := false
def scientificStageOpened : Bool := false
def compatibilityCellsAdjudicated : Bool := false
def gravitationalActionSelected : Bool := false
def evidencePromoted : Bool := false
def scientificSuccessorAuthorized : Bool := false

theorem authority_is_exactly_preparation_only :
    authorizedTarget =
      "prepare_toe_native_gravitational_requirements_and_candidate_action_family_survey_bounded_program_v0" ∧
    selectedFrontier =
      "HYP_TOE_NATIVE_GRAVITATIONAL_PRINCIPLE_ACTION_SELECTION_v0" ∧
    proposalPreparationAuthorized = true ∧
    programInstalled = false ∧
    scientificStageOpened = false ∧
    compatibilityCellsAdjudicated = false ∧
    gravitationalActionSelected = false ∧
    evidencePromoted = false ∧
    scientificSuccessorAuthorized = false := by
  decide

end ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyPreparationAuthorityV0
end Derivation
end ToeFormal
