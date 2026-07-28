import ToeFormal.Derivation.QFTGRQuadraticHyperbolicityAdmissibleSourceAndFrozenTheoryPacketResultReviewV0

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
  QFTGRQuadraticHyperbolicityAdmissibleSourceAndFrozenTheoryPacketResultReviewV0.selectedNextTarget

def currentEvidencePacketId : String :=
  QFTGRQuadraticHyperbolicityAdmissibleSourceAndFrozenTheoryPacketResultReviewV0.reviewId

theorem current_target_is_quadratic_physical_spin2_principal_block :
    currentLiveTarget =
      "derive_qft_gr_quadratic_physical_spin2_principal_block_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
