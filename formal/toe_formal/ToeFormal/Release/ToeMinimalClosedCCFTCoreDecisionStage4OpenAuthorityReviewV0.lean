import ToeFormal.Release.ToeMinimalClosedCCFTCoreDecisionStage4OpenAuthorityV0

namespace ToeFormal
namespace Release
namespace ToeMinimalClosedCCFTCoreDecisionStage4OpenAuthorityReviewV0

def reviewId : String :=
  "TOE_MINIMAL_CLOSED_CCFT_CORE_DECISION_STAGE_4_OPEN_AUTHORITY_REVIEW_v0"
def accepted : Bool := true
def stageFourScientificResultCreated : Bool := false
def coreSelectionResultCreated : Bool := false
def minimalCoreSelected : Bool := false
def physicalCCFTModelOrClaimEstablished : Bool := false
def stageFiveAuthorized : Bool := false

theorem review_accepts_only_narrow_stage_four_open_authority :
    accepted = true ∧ stageFourScientificResultCreated = false ∧
    coreSelectionResultCreated = false ∧ minimalCoreSelected = false ∧
    physicalCCFTModelOrClaimEstablished = false ∧
    stageFiveAuthorized = false ∧
    ToeMinimalClosedCCFTCoreDecisionStage4OpenAuthorityV0.stageFourOpenAuthorized =
      true := by
  decide

end ToeMinimalClosedCCFTCoreDecisionStage4OpenAuthorityReviewV0
end Release
end ToeFormal
