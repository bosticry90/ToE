namespace ToeFormal
namespace Release
namespace ToeRepositoryWideNativeHypothesisClaimExtractionStage3OpenAuthorityV0

def programId : String :=
  "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0"

def semanticStageId : String :=
  "NATIVE_CLAIM_EXTRACTION_AND_CLASSIFICATION"

def target : String :=
  "extract_and_classify_toe_repository_wide_native_hypothesis_claims_v0"

def stageNumber : Nat := 3
def attemptNumber : Nat := 3
def stageTwoSelectedFileCount : Nat := 640
def stageTwoExactDuplicateGroupCount : Nat := 421
def stageTwoEstablishedRelationshipCount : Nat := 35
def stageTwoUnresolvedRelationshipCount : Nat := 16
def maximumDeepReviewFiles : Nat := 640
def maximumFilesPerSourceLineage : Nat := 8
def maximumClaimsPerFile : Nat := 32
def maximumExtractedClaims : Nat := 4096
def stageOpenAuthorized : Bool := true
def scientificTruthAdjudicationAuthorized : Bool := false
def evidencePromotionAuthorized : Bool := false
def nativeFrontierSelectionAuthorized : Bool := false
def automaticStageFourOpenAuthorized : Bool := false

theorem authority_is_bounded_source_bound_claim_extraction_only :
    stageOpenAuthorized = true ∧
    stageNumber = 3 ∧
    attemptNumber = 3 ∧
    stageTwoSelectedFileCount = 640 ∧
    stageTwoExactDuplicateGroupCount = 421 ∧
    stageTwoEstablishedRelationshipCount = 35 ∧
    stageTwoUnresolvedRelationshipCount = 16 ∧
    maximumDeepReviewFiles = 640 ∧
    maximumFilesPerSourceLineage = 8 ∧
    maximumClaimsPerFile = 32 ∧
    maximumExtractedClaims = 4096 ∧
    scientificTruthAdjudicationAuthorized = false ∧
    evidencePromotionAuthorized = false ∧
    nativeFrontierSelectionAuthorized = false ∧
    automaticStageFourOpenAuthorized = false := by
  decide

end ToeRepositoryWideNativeHypothesisClaimExtractionStage3OpenAuthorityV0
end Release
end ToeFormal
