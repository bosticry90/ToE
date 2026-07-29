import ToeFormal.Derivation.QFTGRQuadraticGenericBackgroundLinearizationGaugeAndJetContractResultReviewV0

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
  QFTGRQuadraticGenericBackgroundLinearizationGaugeAndJetContractResultReviewV0.selectedNextTarget

def currentEvidencePacketId : String :=
  QFTGRQuadraticGenericBackgroundLinearizationGaugeAndJetContractResultReviewV0.reviewId

def currentBoundedProgramId : String :=
  "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0"

def currentBoundedProgramState : String := "CLOSED"

def currentBoundedAttemptNumber : Nat := 1

def lastClosedBoundedSemanticStage : String :=
  "STRICT_HARMONIC_GAUGE_JET_CONTRACT"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_is_bounded_quadratic_component_expansion_v1 :
    currentLiveTarget =
      "derive_qft_gr_quadratic_component_expanded_generic_background_linearization_v1" := by
  rfl

theorem first_bounded_quadratic_attempt_is_closed_passed :
    currentBoundedProgramState = "CLOSED" ∧
    currentBoundedAttemptNumber = 1 ∧
    lastBoundedTerminalResult = "PASSED" := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
