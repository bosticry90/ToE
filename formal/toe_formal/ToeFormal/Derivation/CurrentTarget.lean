import ToeFormal.Derivation.ToeNativeSurrogateV0BoundedProgramAuthorization

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
  ToeNativeSurrogateV0BoundedProgramAuthorization.authorizationId

def currentBoundedProgramId : String :=
  "TOE_NATIVE_SURROGATE_V0"

def currentBoundedProgramState : String := "UNOPENED"

def currentBoundedAttemptNumber : Nat := 0

def lastClosedBoundedSemanticStage : String :=
  "NONE"

def lastBoundedTerminalResult : String := "NONE"

theorem current_target_selects_native_coherence_representation_stage :
    currentLiveTarget =
      "select_toe_native_coherence_representation_v0" := by
  rfl

theorem native_program_is_authorized_but_stage_one_is_unopened :
    currentBoundedProgramState = "UNOPENED" ∧
    currentBoundedAttemptNumber = 0 ∧
    lastClosedBoundedSemanticStage = "NONE" ∧
    lastBoundedTerminalResult = "NONE" := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
