namespace ToeFormal
namespace Release
namespace ToeRepositoryWideNativeHypothesisSourceCensusStage1OpenAuthorityV0

def programId : String :=
  "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0"

def semanticStageId : String := "REPOSITORY_WIDE_SOURCE_CENSUS"
def target : String :=
  "inventory_toe_repository_wide_native_hypothesis_sources_v0"

def stageNumber : Nat := 1
def batchCount : Nat := 8
def stageOpenAuthorized : Bool := true
def claimExtractionAuthorized : Bool := false
def evidencePromotionAuthorized : Bool := false
def lineageConclusionAuthorized : Bool := false
def frontierSelectionAuthorized : Bool := false

theorem authority_is_source_custody_only :
    stageOpenAuthorized = true ∧
    stageNumber = 1 ∧
    batchCount = 8 ∧
    claimExtractionAuthorized = false ∧
    evidencePromotionAuthorized = false ∧
    lineageConclusionAuthorized = false ∧
    frontierSelectionAuthorized = false := by
  decide

end ToeRepositoryWideNativeHypothesisSourceCensusStage1OpenAuthorityV0
end Release
end ToeFormal
