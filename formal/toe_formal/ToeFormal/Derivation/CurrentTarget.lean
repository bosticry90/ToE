import ToeFormal.Derivation.QFTGRQuadraticToeRoleAfterGenericFrozenResultV0

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
  "authorize_toe_native_surrogate_v0_bounded_program"

def currentEvidencePacketId : String :=
  QFTGRQuadraticToeRoleAfterGenericFrozenResultV0.calculationId

def currentBoundedProgramId : String :=
  "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0"

def currentBoundedProgramState : String := "TERMINAL"

def currentBoundedAttemptNumber : Nat := 3

def lastClosedBoundedSemanticStage : String :=
  "EXACT_FROZEN_COMPANION_OPERATOR"

def lastBoundedTerminalResult : String := "BLOCKED"

theorem current_target_authorizes_native_bounded_program_installation :
    currentLiveTarget =
      "authorize_toe_native_surrogate_v0_bounded_program" := by
  rfl

theorem quadratic_program_is_terminal_after_role_gate :
    currentBoundedProgramState = "TERMINAL" ∧
    currentBoundedAttemptNumber = 3 ∧
    lastClosedBoundedSemanticStage = "EXACT_FROZEN_COMPANION_OPERATOR" ∧
    lastBoundedTerminalResult = "BLOCKED" := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
