import ToeFormal.Derivation.QFTGRQuadraticExactGenericFrozenCompanionOperatorResultReviewV0

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
  QFTGRQuadraticExactGenericFrozenCompanionOperatorResultReviewV0.selectedNextTarget

def currentEvidencePacketId : String :=
  QFTGRQuadraticExactGenericFrozenCompanionOperatorResultReviewV0.reviewId

theorem current_target_is_quadratic_component_expanded_background :
    currentLiveTarget =
      "derive_qft_gr_quadratic_component_expanded_generic_background_linearization_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
