namespace ToeFormal
namespace Release
namespace ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityV0

def authorityId : String :=
  "TOE_TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_STAGE_1_OPEN_AUTHORITY_v0"
def decision : String :=
  "AUTHORIZE_TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_STAGE_1_OPEN"
def programId : String := "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0"
def semanticStageId : String :=
  "TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY"
def target : String := "discover_toe_targeted_ccft_closure_evidence_sources_v0"
def canonicalScopeHash : String :=
  "d2019a5d75347897cf4648ec88945b2a4cc2209be10ececf6e6c5b7f33d5d6aa"
def authorizedSourceCount : Nat := 7
def authorizedSourceRootCount : Nat := 8
def deepReviewFileCeiling : Nat := 96
def deepReviewByteCeiling : Nat := 536870912
def searchPassesConsumedAtOpen : Nat := 0
def stageOneOpenAuthorized : Bool := true
def scientificResultCreated : Bool := false
def candidateSourceSetCreated : Bool := false
def closureContractRecoveredOrRejected : Bool := false
def ccftRepairOrConstructionAuthorized : Bool := false
def stageTwoAuthorized : Bool := false

theorem authority_is_narrow_custody_only_and_nonconstructive :
    stageOneOpenAuthorized = true ∧ authorizedSourceCount = 7 ∧
    authorizedSourceRootCount = 8 ∧ deepReviewFileCeiling = 96 ∧
    deepReviewByteCeiling = 536870912 ∧ searchPassesConsumedAtOpen = 0 ∧
    scientificResultCreated = false ∧ candidateSourceSetCreated = false ∧
    closureContractRecoveredOrRejected = false ∧
    ccftRepairOrConstructionAuthorized = false ∧ stageTwoAuthorized = false := by
  decide

end ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityV0
end Release
end ToeFormal
