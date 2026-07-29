import ToeFormal.Derivation.ToeNativeHypothesisFrontierSelectionResultReview

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
  "prepare_toe_native_coherence_ontology_and_representation_bounded_program_v0"

def currentEvidencePacketId : String :=
  ToeNativeHypothesisFrontierSelectionResultReview.reviewId

def currentBoundedProgramId : String :=
  "NONE_NEW_PROGRAM_INSTALLED"

def currentBoundedProgramState : String := "NONE_NEW_PROGRAM_INSTALLED"

def currentTargetPhase : String := "PROGRAM_PROPOSAL_PREPARATION_ONLY"

def currentBoundedAttemptNumber : Nat := 0

def lastClosedBoundedSemanticStage : String :=
  "COHERENCE_REPRESENTATION"

def lastBoundedTerminalResult : String := "BLOCKED"

theorem current_target_prepares_native_coherence_ontology_program :
    currentLiveTarget =
      "prepare_toe_native_coherence_ontology_and_representation_bounded_program_v0" := by
  rfl

theorem program_preparation_installs_no_new_bounded_program :
    currentBoundedProgramId = "NONE_NEW_PROGRAM_INSTALLED" ∧
    currentBoundedProgramState = "NONE_NEW_PROGRAM_INSTALLED" ∧
    currentTargetPhase = "PROGRAM_PROPOSAL_PREPARATION_ONLY" ∧
    currentBoundedAttemptNumber = 0 ∧
    lastClosedBoundedSemanticStage = "COHERENCE_REPRESENTATION" ∧
    lastBoundedTerminalResult = "BLOCKED" := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
