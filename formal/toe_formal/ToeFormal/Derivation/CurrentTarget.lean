import ToeFormal.Derivation.ToeNativeHypothesisSourceLineageReconstructionAttemptOpen
import ToeFormal.Derivation.ToeRepositoryWideNativeHypothesisSourceCensusResult

/-
Thin current-target aggregate for tiered validation. This target follows the
live strict target and avoids requiring a full ToeFormal aggregate build for
routine packet checks.
-/

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeNativeHypothesisSourceLineageReconstructionAttemptOpen

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  ToeNativeHypothesisSourceLineageReconstructionAttemptOpen.target

def currentEvidencePacketId : String :=
  ToeNativeHypothesisSourceLineageReconstructionAttemptOpen.evidenceId

def currentBoundedProgramId : String :=
  ToeNativeHypothesisSourceLineageReconstructionAttemptOpen.programId

def currentBoundedProgramState : String := "OPEN"

def currentTargetPhase : String :=
  "STAGE_2_OPEN_AWAITING_SOURCE_LINEAGE_RECONSTRUCTION_RESULT"

def currentBoundedAttemptNumber : Nat :=
  ToeNativeHypothesisSourceLineageReconstructionAttemptOpen.attemptSequenceNumber

def currentBoundedSemanticStage : String :=
  ToeNativeHypothesisSourceLineageReconstructionAttemptOpen.semanticStageId

def lastClosedBoundedSemanticStage : String :=
  "REPOSITORY_WIDE_SOURCE_CENSUS"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_opens_source_lineage_stage :
    currentLiveTarget =
      "reconstruct_toe_native_hypothesis_source_lineages_v0" := by
  rfl

theorem source_lineage_stage_is_open_after_source_census_close :
    currentBoundedProgramId =
      "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0" ∧
    currentBoundedProgramState = "OPEN" ∧
    currentTargetPhase =
      "STAGE_2_OPEN_AWAITING_SOURCE_LINEAGE_RECONSTRUCTION_RESULT" ∧
    currentBoundedAttemptNumber = 2 ∧
    currentBoundedSemanticStage =
      "DEDUPLICATION_AND_LINEAGE_RECONSTRUCTION" ∧
    lastClosedBoundedSemanticStage = "REPOSITORY_WIDE_SOURCE_CENSUS" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    scientificOutputPresent = false ∧
    lineageResultProduced = false ∧
    claimExtractionPerformed = false ∧
    evidencePromoted = false ∧
    nativeFrontierSelected = false ∧
    stageThreeOpened = false ∧
    ToeRepositoryWideNativeHypothesisSourceCensusResult.claimExtractionPerformed =
      false ∧
    ToeRepositoryWideNativeHypothesisSourceCensusResult.lineageConclusionProduced =
      false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
