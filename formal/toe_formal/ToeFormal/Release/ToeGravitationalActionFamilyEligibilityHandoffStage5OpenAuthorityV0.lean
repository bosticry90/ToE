namespace ToeFormal
namespace Release
namespace ToeGravitationalActionFamilyEligibilityHandoffStage5OpenAuthorityV0

def authorityId : String :=
  "TOE_GRAVITATIONAL_ACTION_FAMILY_ELIGIBILITY_HANDOFF_STAGE_5_OPEN_AUTHORITY_v0"

def programId : String :=
  "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0"

def semanticStageId : String := "CANDIDATE_ACTION_FAMILY_ELIGIBILITY_HANDOFF"
def scientificTarget : String := "select_toe_gravitational_action_family_eligibility_handoff_v0"
def scopeHash : String := "aec6355853132543dff1bf7c4aa90e65718ab1b192d56340efc9d5d584bd6dd8"

def stageNumber : Nat := 5
def familyCount : Nat := 7
def eligibilityClassCount : Nat := 8
def routeClassCount : Nat := 5
def classificationsMade : Nat := 0
def routesSelected : Nat := 0
def actionsSelected : Nat := 0
def principlesSelected : Nat := 0
def successorProgramsAuthorized : Nat := 0

def stageFiveOpenOnly : Bool := true
def actionOrPrincipleAdoptionAuthorized : Bool := false
def gravitationalCalculationAuthorized : Bool := false
def successorExecutionAuthorized : Bool := false

theorem authority_binds_stage_five_without_scientific_result :
    stageNumber = 5 ∧
    familyCount = 7 ∧
    eligibilityClassCount = 8 ∧
    routeClassCount = 5 ∧
    classificationsMade = 0 ∧
    routesSelected = 0 ∧
    actionsSelected = 0 ∧
    principlesSelected = 0 ∧
    successorProgramsAuthorized = 0 ∧
    stageFiveOpenOnly = true ∧
    actionOrPrincipleAdoptionAuthorized = false ∧
    gravitationalCalculationAuthorized = false ∧
    successorExecutionAuthorized = false := by
  decide

end ToeGravitationalActionFamilyEligibilityHandoffStage5OpenAuthorityV0
end Release
end ToeFormal
