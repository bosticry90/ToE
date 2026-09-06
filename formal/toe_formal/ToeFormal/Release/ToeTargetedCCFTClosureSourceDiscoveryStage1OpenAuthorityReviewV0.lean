import ToeFormal.Release.ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityV0

namespace ToeFormal
namespace Release
namespace ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityReviewV0

def reviewId : String :=
  "TOE_TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_STAGE_1_OPEN_AUTHORITY_REVIEW_v0"
def accepted : Bool := true
def scientificResultCreated : Bool := false
def archiveOrRepositoryContentSearched : Bool := false
def candidateSourceSetCreated : Bool := false
def closureContractRecoveredOrRejected : Bool := false
def stageTwoAuthorized : Bool := false

theorem review_accepts_only_narrow_stage_one_open_authority :
    accepted = true ∧ scientificResultCreated = false ∧
    archiveOrRepositoryContentSearched = false ∧
    candidateSourceSetCreated = false ∧
    closureContractRecoveredOrRejected = false ∧ stageTwoAuthorized = false ∧
    ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityV0.stageOneOpenAuthorized =
      true := by
  decide

end ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityReviewV0
end Release
end ToeFormal
