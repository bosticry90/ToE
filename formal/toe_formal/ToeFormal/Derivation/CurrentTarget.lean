import ToeFormal.Derivation.QFTGRQuadraticComponentExpandedGenericBackgroundLinearizationResultReviewV0

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
  QFTGRQuadraticComponentExpandedGenericBackgroundLinearizationResultReviewV0.selectedNextTarget

def currentEvidencePacketId : String :=
  QFTGRQuadraticComponentExpandedGenericBackgroundLinearizationResultReviewV0.reviewId

def currentBoundedProgramId : String :=
  "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0"

def currentBoundedProgramState : String := "OPEN"

def currentBoundedAttemptNumber : Nat := 1

def currentBoundedSemanticStage : String :=
  "STRICT_HARMONIC_GAUGE_JET_CONTRACT"

theorem current_target_is_quadratic_background_gauge_and_jet_contract :
    currentLiveTarget =
      "prepare_qft_gr_quadratic_generic_background_linearization_gauge_and_jet_contract_v0" := by
  rfl

theorem first_bounded_quadratic_attempt_is_open :
    currentBoundedProgramState = "OPEN" ∧
    currentBoundedAttemptNumber = 1 := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
