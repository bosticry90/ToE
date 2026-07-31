namespace ToeFormal
namespace Release
namespace ToeNativeGravitationalRequirementInventoryStage1OpenAuthorityV0

def programId : String :=
  "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0"

def semanticStageId : String :=
  "NATIVE_GRAVITATIONAL_REQUIREMENT_INVENTORY"

def canonicalTarget : String :=
  "inventory_toe_native_gravitational_requirements_v0"

def canonicalScopeHash : String :=
  "297276852be0fed5e7dafdb9a90a3dc26a2807665665dbefc69dd8572b31fb19"

def authorityGranted : Bool := true
def requirementCount : Nat := 10
def stageNumber : Nat := 1
def scientificResultCreated : Bool := false
def candidateFamiliesCompared : Bool := false
def gravitationalActionSelected : Bool := false
def gravitationalCalculationStarted : Bool := false
def stageTwoAuthorized : Bool := false

theorem authority_is_exactly_for_stage_one_open :
    authorityGranted = true ∧
    requirementCount = 10 ∧
    stageNumber = 1 ∧
    scientificResultCreated = false ∧
    candidateFamiliesCompared = false ∧
    gravitationalActionSelected = false ∧
    gravitationalCalculationStarted = false ∧
    stageTwoAuthorized = false := by
  decide

end ToeNativeGravitationalRequirementInventoryStage1OpenAuthorityV0
end Release
end ToeFormal
