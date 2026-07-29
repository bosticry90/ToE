import ToeFormal.Derivation.QFTGRQuadraticFrozenCoefficientJordanChainFrequencyGrowthResultReviewV0

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
  QFTGRQuadraticFrozenCoefficientJordanChainFrequencyGrowthResultReviewV0.selectedNextTarget

def currentEvidencePacketId : String :=
  QFTGRQuadraticFrozenCoefficientJordanChainFrequencyGrowthResultReviewV0.reviewId

theorem current_target_is_quadratic_exact_generic_frozen_companion :
    currentLiveTarget =
      "derive_qft_gr_quadratic_exact_generic_frozen_companion_operator_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
