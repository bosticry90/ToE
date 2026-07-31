namespace ToeFormal
namespace Release
namespace ToeCandidateGravitationalActionFamilyInventoryStage2OpenAuthorityV0

def programId : String :=
  "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0"

def semanticStageId : String :=
  "CANDIDATE_GRAVITATIONAL_ACTION_FAMILY_INVENTORY"

def canonicalTarget : String :=
  "inventory_toe_candidate_gravitational_action_families_v0"

def canonicalScopeHash : String :=
  "8dc24a87cd882d67123278bc2da416a4efffe29866f96bbecc4dd7af7a7942ea"

def authorityGranted : Bool := true
def familyCount : Nat := 7
def stageNumber : Nat := 2
def scientificResultCreated : Bool := false
def actionFamiliesCompared : Bool := false
def gravitationalActionSelected : Bool := false
def gravitationalCalculationStarted : Bool := false
def stageThreeAuthorized : Bool := false

theorem authority_is_exactly_for_stage_two_open :
    authorityGranted = true ∧
    familyCount = 7 ∧
    stageNumber = 2 ∧
    scientificResultCreated = false ∧
    actionFamiliesCompared = false ∧
    gravitationalActionSelected = false ∧
    gravitationalCalculationStarted = false ∧
    stageThreeAuthorized = false := by
  decide

end ToeCandidateGravitationalActionFamilyInventoryStage2OpenAuthorityV0
end Release
end ToeFormal
