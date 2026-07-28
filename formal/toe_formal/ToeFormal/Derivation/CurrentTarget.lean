import ToeFormal.Derivation.QFTGRQuadraticGaugeAndAuxiliaryConstraintPropagationSystemResultReviewV0

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
  QFTGRQuadraticGaugeAndAuxiliaryConstraintPropagationSystemResultReviewV0.selectedNextTarget

def currentEvidencePacketId : String :=
  QFTGRQuadraticGaugeAndAuxiliaryConstraintPropagationSystemResultReviewV0.reviewId

theorem current_target_is_quadratic_full_reduced_principal_structure :
    currentLiveTarget =
      "compute_qft_gr_quadratic_full_reduced_system_principal_structure_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
