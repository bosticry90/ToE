namespace ToeFormal
namespace Release
namespace ToePostCensusNativeFrontierDecisionStage5OpenAuthorityV0

def programId : String :=
  "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0"

def semanticStageId : String :=
  "NATIVE_FRONTIER_DECISION"

def target : String :=
  "select_toe_native_frontier_after_repository_wide_evidence_census_v0"

def stageNumber : Nat := 5
def attemptNumber : Nat := 5
def inputClaimCount : Nat := 2673
def candidateFamilyCount : Nat := 23
def supportedButIncompleteClaimCount : Nat := 77
def maximumRankedCandidates : Nat := 23
def maximumSelectedFrontiers : Nat := 1
def maximumMissingPrerequisitesPerCandidate : Nat := 10
def stageOpenAuthorized : Bool := true
def explicitNoSelectionPermitted : Bool := true
def scientificTruthAdjudicationAuthorized : Bool := false
def canonicalEvidencePromotionAuthorized : Bool := false
def fieldActionOrSeamExecutionAuthorized : Bool := false
def automaticSuccessorProgramOpenAuthorized : Bool := false

theorem authority_is_bounded_one_frontier_or_no_frontier_decision_only :
    stageOpenAuthorized = true ∧
    stageNumber = 5 ∧
    attemptNumber = 5 ∧
    inputClaimCount = 2673 ∧
    candidateFamilyCount = 23 ∧
    supportedButIncompleteClaimCount = 77 ∧
    maximumRankedCandidates = 23 ∧
    maximumSelectedFrontiers = 1 ∧
    maximumMissingPrerequisitesPerCandidate = 10 ∧
    explicitNoSelectionPermitted = true ∧
    scientificTruthAdjudicationAuthorized = false ∧
    canonicalEvidencePromotionAuthorized = false ∧
    fieldActionOrSeamExecutionAuthorized = false ∧
    automaticSuccessorProgramOpenAuthorized = false := by
  decide

end ToePostCensusNativeFrontierDecisionStage5OpenAuthorityV0
end Release
end ToeFormal
