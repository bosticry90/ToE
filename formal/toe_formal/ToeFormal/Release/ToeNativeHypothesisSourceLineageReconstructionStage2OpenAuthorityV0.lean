namespace ToeFormal
namespace Release
namespace ToeNativeHypothesisSourceLineageReconstructionStage2OpenAuthorityV0

def programId : String :=
  "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0"

def semanticStageId : String :=
  "DEDUPLICATION_AND_LINEAGE_RECONSTRUCTION"

def target : String :=
  "reconstruct_toe_native_hypothesis_source_lineages_v0"

def stageNumber : Nat := 2
def attemptNumber : Nat := 2
def stageOneRecordCount : Nat := 13563
def stageOneExactDuplicateGroupCount : Nat := 421
def maximumBoundedSourceComparisonFiles : Nat := 640
def maximumFilesPerSourceLineage : Nat := 8
def maximumUnresolvedLineageRelationships : Nat := 512
def stageOpenAuthorized : Bool := true
def claimExtractionAuthorized : Bool := false
def evidencePromotionAuthorized : Bool := false
def nativeFrontierSelectionAuthorized : Bool := false
def automaticStageThreeOpenAuthorized : Bool := false

theorem authority_is_bounded_source_lineage_only :
    stageOpenAuthorized = true ∧
    stageNumber = 2 ∧
    attemptNumber = 2 ∧
    stageOneRecordCount = 13563 ∧
    stageOneExactDuplicateGroupCount = 421 ∧
    maximumBoundedSourceComparisonFiles = 640 ∧
    maximumFilesPerSourceLineage = 8 ∧
    maximumUnresolvedLineageRelationships = 512 ∧
    claimExtractionAuthorized = false ∧
    evidencePromotionAuthorized = false ∧
    nativeFrontierSelectionAuthorized = false ∧
    automaticStageThreeOpenAuthorized = false := by
  decide

end ToeNativeHypothesisSourceLineageReconstructionStage2OpenAuthorityV0
end Release
end ToeFormal
