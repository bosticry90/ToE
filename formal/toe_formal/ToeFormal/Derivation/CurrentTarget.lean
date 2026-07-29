import ToeFormal.Derivation.QFTGRQuadraticAdaptedDerivativeLossEnergyHierarchyResultReviewV0

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
  QFTGRQuadraticAdaptedDerivativeLossEnergyHierarchyResultReviewV0.selectedNextTarget

def currentEvidencePacketId : String :=
  QFTGRQuadraticAdaptedDerivativeLossEnergyHierarchyResultReviewV0.reviewId

theorem current_target_is_quadratic_frozen_jordan_frequency_growth :
    currentLiveTarget =
      "compute_qft_gr_quadratic_frozen_coefficient_jordan_chain_frequency_growth_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
