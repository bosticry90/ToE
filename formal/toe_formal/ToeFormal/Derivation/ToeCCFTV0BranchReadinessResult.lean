namespace ToeFormal
namespace Derivation
namespace ToeCCFTV0BranchReadinessResult

def resultId : String := "TOE_CCFT_V0_RESEARCH_DIRECTOR_BRANCH_READINESS_DECISION_RESULT_v0"
def reviewId : String := "TOE_CCFT_V0_RESEARCH_DIRECTOR_BRANCH_READINESS_DECISION_RESULT_REVIEW_v0"
def programId : String := "TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0"
def semanticStageId : String := "CCFT_V0_RESEARCH_DIRECTOR_BRANCH_READINESS_DECISION"
def selectedOutcome : String := "SELECT_CP_NLSE_AS_CCFT_V0_CORE"
def selectedBranch : String := "CP_NLSE"
def proposedStageTwoTarget : String := "complete_and_freeze_toe_ccft_v0_model_contract_v0"
def attemptSequenceNumber : Nat := 1
def exactSelectedOutcomeCount : Nat := 1
def preservedCPNLSEConflictCount : Nat := 3
def maximumNewPostulates : Nat := 8
def maximumFrozenModels : Nat := 1
def governingEquationSelected : Bool := false
def newPostulateCreated : Bool := false
def modelConstructed : Bool := false
def theoremSelectedOrAttempted : Bool := false
def lcrdRejected : Bool := false
def stageTwoAuthorized : Bool := false

theorem stage_one_selects_only_the_cp_nlse_construction_route :
    selectedOutcome = "SELECT_CP_NLSE_AS_CCFT_V0_CORE" ∧
    selectedBranch = "CP_NLSE" ∧ exactSelectedOutcomeCount = 1 ∧
    preservedCPNLSEConflictCount = 3 ∧ maximumNewPostulates = 8 ∧
    maximumFrozenModels = 1 ∧ governingEquationSelected = false ∧
    newPostulateCreated = false ∧ modelConstructed = false ∧
    theoremSelectedOrAttempted = false ∧ lcrdRejected = false ∧
    stageTwoAuthorized = false := by
  decide

end ToeCCFTV0BranchReadinessResult
end Derivation
end ToeFormal
