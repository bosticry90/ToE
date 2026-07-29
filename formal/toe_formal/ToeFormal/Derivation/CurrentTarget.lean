import ToeFormal.Derivation.QFTGRQuadraticExactGenericFrozenCompanionOperatorV1

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
  "select_qft_gr_quadratic_toe_role_after_generic_frozen_result_v0"

def currentEvidencePacketId : String :=
  QFTGRQuadraticExactGenericFrozenCompanionOperatorV1.calculationId

def currentBoundedProgramId : String :=
  "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0"

def currentBoundedProgramState : String := "CLOSED"

def currentBoundedAttemptNumber : Nat := 3

def lastClosedBoundedSemanticStage : String :=
  "EXACT_FROZEN_COMPANION_OPERATOR"

def lastBoundedTerminalResult : String := "BLOCKED"

theorem current_target_is_mandatory_quadratic_role_gate :
    currentLiveTarget =
      "select_qft_gr_quadratic_toe_role_after_generic_frozen_result_v0" := by
  rfl

theorem third_bounded_quadratic_attempt_closed_blocked_and_requires_exit :
    currentBoundedProgramState = "CLOSED" ∧
    currentBoundedAttemptNumber = 3 ∧
    lastClosedBoundedSemanticStage = "EXACT_FROZEN_COMPANION_OPERATOR" ∧
    lastBoundedTerminalResult = "BLOCKED" := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
