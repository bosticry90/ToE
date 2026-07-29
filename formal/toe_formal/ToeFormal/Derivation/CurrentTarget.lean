import ToeFormal.Derivation.ToeNativeCoherenceRepresentationV0AttemptOpen

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
  "select_toe_native_coherence_representation_v0"

def currentEvidencePacketId : String :=
  ToeNativeCoherenceRepresentationV0AttemptOpen.openEventHash

def currentBoundedProgramId : String :=
  "TOE_NATIVE_SURROGATE_V0"

def currentBoundedProgramState : String := "OPEN"

def currentBoundedAttemptNumber : Nat := 1

def lastClosedBoundedSemanticStage : String :=
  "NONE"

def lastBoundedTerminalResult : String := "NONE"

theorem current_target_selects_native_coherence_representation_stage :
    currentLiveTarget =
      "select_toe_native_coherence_representation_v0" := by
  rfl

theorem native_program_stage_one_is_open_without_result :
    currentBoundedProgramState = "OPEN" ∧
    currentBoundedAttemptNumber = 1 ∧
    lastClosedBoundedSemanticStage = "NONE" ∧
    lastBoundedTerminalResult = "NONE" := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
