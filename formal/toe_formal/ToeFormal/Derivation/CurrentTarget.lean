import ToeFormal.Derivation.QFTGRQuadraticAuxiliaryHarmonicReducedSystemResultReviewV0

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
  QFTGRQuadraticAuxiliaryHarmonicReducedSystemResultReviewV0.selectedNextTarget

def currentEvidencePacketId : String :=
  QFTGRQuadraticAuxiliaryHarmonicReducedSystemResultReviewV0.reviewId

theorem current_target_is_quadratic_constraint_propagation_system :
    currentLiveTarget =
      "derive_qft_gr_quadratic_gauge_and_auxiliary_constraint_propagation_system_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
