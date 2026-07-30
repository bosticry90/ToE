import ToeFormal.Derivation.ToeRepositoryWideNativeHypothesisEvidenceCensusBoundedProgramPreparationResultReview

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
  "prepare_toe_repository_wide_native_hypothesis_evidence_census_bounded_program_v0"

def currentEvidencePacketId : String :=
  ToeRepositoryWideNativeHypothesisEvidenceCensusBoundedProgramPreparationResultReview.calculationId

def currentBoundedProgramId : String :=
  "NONE_NEW_PROGRAM_INSTALLED"

def currentBoundedProgramState : String := "NONE_NEW_PROGRAM_INSTALLED"

def currentTargetPhase : String :=
  "PROGRAM_PROPOSAL_PREPARED_AWAITING_SEPARATE_AUTHORITY"

def currentBoundedAttemptNumber : Nat := 0

def lastClosedBoundedSemanticStage : String :=
  "COHERENCE_OPERATIONAL_DEFINITION_TEST"

def lastBoundedTerminalResult : String := "BLOCKED"

theorem current_target_prepares_repository_wide_evidence_census :
    currentLiveTarget =
      "prepare_toe_repository_wide_native_hypothesis_evidence_census_bounded_program_v0" := by
  rfl

theorem prepared_census_proposal_installs_no_new_bounded_program :
    currentBoundedProgramId =
      "NONE_NEW_PROGRAM_INSTALLED" ∧
    currentBoundedProgramState = "NONE_NEW_PROGRAM_INSTALLED" ∧
    currentTargetPhase =
      "PROGRAM_PROPOSAL_PREPARED_AWAITING_SEPARATE_AUTHORITY" ∧
    currentBoundedAttemptNumber = 0 ∧
    lastClosedBoundedSemanticStage =
      "COHERENCE_OPERATIONAL_DEFINITION_TEST" ∧
    lastBoundedTerminalResult = "BLOCKED" := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
