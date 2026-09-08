namespace ToeFormal
namespace Release
namespace ToeCCFTSourceBoundMathematicalInventoryStage1OpenAuthorityV0

def authorityId : String :=
  "TOE_CCFT_SOURCE_BOUND_MATHEMATICAL_INVENTORY_STAGE_1_OPEN_AUTHORITY_v0"
def decision : String :=
  "AUTHORIZE_CCFT_SOURCE_BOUND_MATHEMATICAL_INVENTORY_STAGE_1_OPEN"
def programId : String :=
  "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_V0"
def semanticStageId : String := "CCFT_SOURCE_BOUND_MATHEMATICAL_INVENTORY"
def target : String := "inventory_toe_source_bound_ccft_mathematical_structures_v0"
def canonicalScopeHash : String :=
  "e348568927073147b6353de85f14a13c2e332f217677d8e7c16a0cc7cac0d53e"
def authorizedSourceCount : Nat := 10
def deepReviewSourceCeiling : Nat := 160
def extractedStatementCeiling : Nat := 1024
def stageOneOpenAuthorized : Bool := true
def scientificResultCreated : Bool := false
def physicalInterpretationAuthorized : Bool := false
def modelConstructionAuthorized : Bool := false
def stageTwoAuthorized : Bool := false

theorem authority_is_narrow_noninterpreting_and_nonconstructive :
    stageOneOpenAuthorized = true ∧ authorizedSourceCount = 10 ∧
    deepReviewSourceCeiling = 160 ∧ extractedStatementCeiling = 1024 ∧
    scientificResultCreated = false ∧
    physicalInterpretationAuthorized = false ∧
    modelConstructionAuthorized = false ∧ stageTwoAuthorized = false := by
  decide

end ToeCCFTSourceBoundMathematicalInventoryStage1OpenAuthorityV0
end Release
end ToeFormal
