namespace ToeFormal
namespace Release
namespace ToeCCFTV0ModelContractFreezeStage2OpenAuthorityV0

def authorityId : String :=
  "TOE_CCFT_V0_MODEL_CONTRACT_COMPLETION_AND_FREEZE_STAGE_2_OPEN_AUTHORITY_v0"
def programId : String := "TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0"
def semanticStageId : String := "CCFT_V0_MODEL_CONTRACT_COMPLETION_AND_FREEZE"
def selectedBranch : String := "CP_NLSE"
def stageNumber : Nat := 2
def maximumFrozenModels : Nat := 1
def maximumNewPostulates : Nat := 8
def provenanceLabelCount : Nat := 5
def stageTwoOpenAuthorized : Bool := true
def governingEquationSelected : Bool := false
def newPostulateCreated : Bool := false
def modelConstructed : Bool := false
def theoremWorkAuthorized : Bool := false
def stageThreeAuthorized : Bool := false

theorem authority_opens_bounded_model_construction_without_precomputed_model :
    selectedBranch = "CP_NLSE" ∧ stageNumber = 2 ∧ maximumFrozenModels = 1 ∧
    maximumNewPostulates = 8 ∧ provenanceLabelCount = 5 ∧
    stageTwoOpenAuthorized = true ∧ governingEquationSelected = false ∧
    newPostulateCreated = false ∧ modelConstructed = false ∧
    theoremWorkAuthorized = false ∧ stageThreeAuthorized = false := by
  decide

end ToeCCFTV0ModelContractFreezeStage2OpenAuthorityV0
end Release
end ToeFormal
