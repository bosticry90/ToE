namespace ToeFormal
namespace Release
namespace ToeTargetedCCFTClosureContractExtractionStage2OpenAuthorityV0

def authorityId : String :=
  "TOE_TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_STAGE_2_OPEN_AUTHORITY_v0"
def decision : String :=
  "AUTHORIZE_TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_STAGE_2_OPEN"
def programId : String := "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0"
def semanticStageId : String := "TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION"
def target : String := "extract_toe_targeted_ccft_closure_contracts_v0"
def canonicalScopeHash : String :=
  "bf5a69abf0b8c49b1f5806afa6483a205201103126921af60fef6476348bb0e0"
def selectedSourceCount : Nat := 96
def cpNlseSelectedSourceCount : Nat := 48
def lcrdV3SelectedSourceCount : Nat := 48
def evidenceClassCount : Nat := 7
def missingContractCount : Nat := 18
def contentSearchPassesConsumed : Nat := 1
def contractRecordsAtAuthority : Nat := 0
def stageTwoOpenAuthorized : Bool := true
def scientificResultCreated : Bool := false
def contractRecoveredOrRejected : Bool := false
def secondSearchOrOverflowSubstitutionAuthorized : Bool := false
def ccftRepairOrConstructionAuthorized : Bool := false
def stageThreeAuthorized : Bool := false

theorem authority_is_bounded_to_extraction_and_nonconstructive :
    stageTwoOpenAuthorized = true ∧ selectedSourceCount = 96 ∧
    cpNlseSelectedSourceCount = 48 ∧ lcrdV3SelectedSourceCount = 48 ∧
    evidenceClassCount = 7 ∧ missingContractCount = 18 ∧
    contentSearchPassesConsumed = 1 ∧ contractRecordsAtAuthority = 0 ∧
    scientificResultCreated = false ∧ contractRecoveredOrRejected = false ∧
    secondSearchOrOverflowSubstitutionAuthorized = false ∧
    ccftRepairOrConstructionAuthorized = false ∧ stageThreeAuthorized = false := by
  decide

end ToeTargetedCCFTClosureContractExtractionStage2OpenAuthorityV0
end Release
end ToeFormal
