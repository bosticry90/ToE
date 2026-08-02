namespace ToeFormal
namespace Release
namespace ToeCCFTV0BranchReadinessStage1OpenAuthorityV0

def authorityId : String :=
  "TOE_CCFT_V0_RESEARCH_DIRECTOR_BRANCH_READINESS_DECISION_STAGE_1_OPEN_AUTHORITY_v0"
def programId : String := "TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0"
def semanticStageId : String := "CCFT_V0_RESEARCH_DIRECTOR_BRANCH_READINESS_DECISION"
def stageNumber : Nat := 1
def canonicalOutcomeCount : Nat := 4
def blockingOutcomeCount : Nat := 2
def scientificStageOpenAuthorized : Bool := true
def branchSelected : Bool := false
def modelConstructed : Bool := false
def postulateCreated : Bool := false
def theoremAttempted : Bool := false
def stageTwoAuthorized : Bool := false

theorem authority_opens_only_the_branch_decision :
    stageNumber = 1 ∧ canonicalOutcomeCount = 4 ∧ blockingOutcomeCount = 2 ∧
    scientificStageOpenAuthorized = true ∧ branchSelected = false ∧
    modelConstructed = false ∧ postulateCreated = false ∧
    theoremAttempted = false ∧ stageTwoAuthorized = false := by
  decide

end ToeCCFTV0BranchReadinessStage1OpenAuthorityV0
end Release
end ToeFormal
