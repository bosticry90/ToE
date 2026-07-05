import ToeFormal.Derivation.SelectedCCFTEmpiricalDiscriminatorBaselineComponentEquationSourceClassificationPacketResultReview

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
  SelectedCCFTEmpiricalDiscriminatorBaselineComponentEquationSourceClassificationPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  SelectedCCFTEmpiricalDiscriminatorBaselineComponentEquationSourceClassificationPacketResultReview.packetId

theorem current_target_points_to_selected_ccft_empirical_discriminator_baseline_component_equation_source_validation_criteria_packet :
    currentLiveTarget =
      "prepare_selected_ccft_empirical_discriminator_baseline_component_equation_source_validation_criteria_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
