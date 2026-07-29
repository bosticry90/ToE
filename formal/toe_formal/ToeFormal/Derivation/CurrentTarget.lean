import ToeFormal.Derivation.QFTGRQuadraticFullReducedSystemPrincipalStructureResultReviewV0

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
  QFTGRQuadraticFullReducedSystemPrincipalStructureResultReviewV0.selectedNextTarget

def currentEvidencePacketId : String :=
  QFTGRQuadraticFullReducedSystemPrincipalStructureResultReviewV0.reviewId

theorem current_target_is_quadratic_adapted_energy_hierarchy_preparation :
    currentLiveTarget =
      "prepare_qft_gr_quadratic_adapted_derivative_loss_energy_hierarchy_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
