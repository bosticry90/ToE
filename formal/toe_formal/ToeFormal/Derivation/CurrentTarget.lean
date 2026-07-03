import ToeFormal.Derivation.SelectedCCFTEmpiricalDiscriminatorToleranceRegistryPacketResultReview

/-
Thin current-target aggregate for tiered validation. This target follows the
live strict target and avoids requiring a full ToeFormal aggregate build for
routine packet checks.
-/

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

set_option linter.style.longLine false

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  SelectedCCFTEmpiricalDiscriminatorToleranceRegistryPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  SelectedCCFTEmpiricalDiscriminatorToleranceRegistryPacketResultReview.packetId

theorem current_target_points_to_selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet :
    currentLiveTarget =
      "prepare_selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
