import ToeFormal.Derivation.SelectedCCFTEmpiricalDiscriminatorBaselineComponentInteractionRiskPacketResultReview

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
  SelectedCCFTEmpiricalDiscriminatorBaselineComponentInteractionRiskPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  SelectedCCFTEmpiricalDiscriminatorBaselineComponentInteractionRiskPacketResultReview.packetId

theorem current_target_points_to_selected_ccft_empirical_discriminator_baseline_construction_obligation_packet :
    currentLiveTarget =
      "prepare_selected_ccft_empirical_discriminator_baseline_construction_obligation_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
