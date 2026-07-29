import ToeFormal.Derivation.ToeNativeHypothesisFrontierSelectionAuthority

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
  "select_next_native_toe_hypothesis_for_bounded_adjudication_v0"

def currentEvidencePacketId : String :=
  ToeNativeHypothesisFrontierSelectionAuthority.packetId

def currentBoundedProgramId : String :=
  "NONE_NEW_PROGRAM_INSTALLED"

def currentBoundedProgramState : String := "SELECTION_ONLY"

def currentBoundedAttemptNumber : Nat := 0

def lastClosedBoundedSemanticStage : String :=
  "COHERENCE_REPRESENTATION"

def lastBoundedTerminalResult : String := "BLOCKED"

theorem current_target_selects_native_hypothesis_frontier_decision :
    currentLiveTarget =
      "select_next_native_toe_hypothesis_for_bounded_adjudication_v0" := by
  rfl

theorem selector_installs_no_new_bounded_program :
    currentBoundedProgramId = "NONE_NEW_PROGRAM_INSTALLED" ∧
    currentBoundedProgramState = "SELECTION_ONLY" ∧
    currentBoundedAttemptNumber = 0 ∧
    lastClosedBoundedSemanticStage = "COHERENCE_REPRESENTATION" ∧
    lastBoundedTerminalResult = "BLOCKED" := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
