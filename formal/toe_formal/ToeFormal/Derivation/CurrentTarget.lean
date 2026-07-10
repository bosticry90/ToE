import ToeFormal.Derivation.ScalarStressEnergyDivergenceIdentityMinkowskiCalculationResultReview

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
  ScalarStressEnergyDivergenceIdentityMinkowskiCalculationResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  ScalarStressEnergyDivergenceIdentityMinkowskiCalculationResultReview.reviewId

theorem current_target_points_to_bounded_curved_retest_guardrail :
    currentLiveTarget =
      "prepare_bounded_curved_space_scalar_qft_gr_source_contract_retest_guardrail_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
