import ToeFormal.Derivation.QFTGRQuadraticPhysicalSpin2PrincipalBlockResultReviewV0

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
  QFTGRQuadraticPhysicalSpin2PrincipalBlockResultReviewV0.selectedNextTarget

def currentEvidencePacketId : String :=
  QFTGRQuadraticPhysicalSpin2PrincipalBlockResultReviewV0.reviewId

theorem current_target_is_quadratic_auxiliary_harmonic_adapted_norm_packet :
    currentLiveTarget =
      "prepare_qft_gr_quadratic_auxiliary_harmonic_adapted_norm_well_posedness_packet_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
