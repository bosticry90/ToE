import ToeFormal.Derivation.QFTGRQuadraticStageThreeCanonicalTargetIdentifierCorrectionV0

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
  QFTGRQuadraticStageThreeCanonicalTargetIdentifierCorrectionV0.canonicalStageTarget

def currentEvidencePacketId : String :=
  QFTGRQuadraticStageThreeCanonicalTargetIdentifierCorrectionV0.correctionId

def currentBoundedProgramId : String :=
  "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0"

def currentBoundedProgramState : String := "OPEN"

def currentBoundedAttemptNumber : Nat := 3

def lastClosedBoundedSemanticStage : String :=
  "COMPONENT_EXPANDED_LINEARIZATION"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_is_bounded_quadratic_exact_companion_v1 :
    currentLiveTarget =
      "derive_qft_gr_quadratic_exact_generic_frozen_companion_operator_v1" := by
  rfl

theorem third_bounded_quadratic_attempt_is_open_after_second_closed_passed :
    currentBoundedProgramState = "OPEN" ∧
    currentBoundedAttemptNumber = 3 ∧
    lastClosedBoundedSemanticStage = "COMPONENT_EXPANDED_LINEARIZATION" ∧
    lastBoundedTerminalResult = "PASSED" := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
