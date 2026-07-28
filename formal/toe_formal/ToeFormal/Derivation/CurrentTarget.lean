import ToeFormal.Derivation.QFTGRQuadraticHyperbolicityBoundedReconciliationSelectionResultReviewV0

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
  QFTGRQuadraticHyperbolicityBoundedReconciliationSelectionResultReviewV0.selectedNextTarget

def currentEvidencePacketId : String :=
  QFTGRQuadraticHyperbolicityBoundedReconciliationSelectionResultReviewV0.reviewId

theorem current_target_is_fresh_quadratic_hyperbolicity_source_packet :
    currentLiveTarget =
      "prepare_qft_gr_quadratic_hyperbolicity_admissible_source_and_frozen_theory_packet_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
