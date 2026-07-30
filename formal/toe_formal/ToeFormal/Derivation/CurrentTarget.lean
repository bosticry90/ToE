import ToeFormal.Derivation.ToeRepositoryWideNativeHypothesisSourceCensusAttemptOpen

/-
Thin current-target aggregate for tiered validation. This target follows the
live strict target and avoids requiring a full ToeFormal aggregate build for
routine packet checks.
-/

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  ToeRepositoryWideNativeHypothesisSourceCensusAttemptOpen.target

def currentEvidencePacketId : String :=
  ToeRepositoryWideNativeHypothesisSourceCensusAttemptOpen.evidenceId

def currentBoundedProgramId : String :=
  ToeRepositoryWideNativeHypothesisSourceCensusAttemptOpen.programId

def currentBoundedProgramState : String := "OPEN"

def currentTargetPhase : String :=
  "REPOSITORY_WIDE_SOURCE_CENSUS_STAGE_1_OPEN"

def currentBoundedAttemptNumber : Nat :=
  ToeRepositoryWideNativeHypothesisSourceCensusAttemptOpen.attemptSequenceNumber

def lastClosedBoundedSemanticStage : String :=
  "COHERENCE_OPERATIONAL_DEFINITION_TEST"

def lastBoundedTerminalResult : String := "BLOCKED"

theorem current_target_opens_repository_wide_source_census :
    currentLiveTarget =
      "inventory_toe_repository_wide_native_hypothesis_sources_v0" := by
  rfl

theorem repository_wide_source_census_is_open_without_scientific_output :
    currentBoundedProgramId =
      "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0" ∧
    currentBoundedProgramState = "OPEN" ∧
    currentTargetPhase =
      "REPOSITORY_WIDE_SOURCE_CENSUS_STAGE_1_OPEN" ∧
    currentBoundedAttemptNumber = 1 ∧
    ToeRepositoryWideNativeHypothesisSourceCensusAttemptOpen.scientificOutputPresent =
      false ∧
    ToeRepositoryWideNativeHypothesisSourceCensusAttemptOpen.archiveScientificallyTraversed =
      false ∧
    ToeRepositoryWideNativeHypothesisSourceCensusAttemptOpen.authoritativeCensusIndexGenerated =
      false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
