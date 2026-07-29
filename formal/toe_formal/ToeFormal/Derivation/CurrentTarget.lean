import ToeFormal.Derivation.ToeNativeCoherenceRepresentationV0ResultReview

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
  "close_toe_native_surrogate_v0_after_bounded_result_v0"

def currentEvidencePacketId : String :=
  ToeNativeCoherenceRepresentationV0ResultReview.calculationId

def currentBoundedProgramId : String :=
  "TOE_NATIVE_SURROGATE_V0"

def currentBoundedProgramState : String := "CLOSED"

def currentBoundedAttemptNumber : Nat := 1

def lastClosedBoundedSemanticStage : String :=
  "COHERENCE_REPRESENTATION"

def lastBoundedTerminalResult : String := "BLOCKED"

theorem current_target_selects_native_surrogate_mandatory_closeout :
    currentLiveTarget =
      "close_toe_native_surrogate_v0_after_bounded_result_v0" := by
  rfl

theorem native_program_stage_one_is_closed_and_blocked :
    currentBoundedProgramState = "CLOSED" ∧
    currentBoundedAttemptNumber = 1 ∧
    lastClosedBoundedSemanticStage = "COHERENCE_REPRESENTATION" ∧
    lastBoundedTerminalResult = "BLOCKED" := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
