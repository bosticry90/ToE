import ToeFormal.Derivation.SelectedCCFTEmpiricalDiscriminatorBaselineComponentEquationSourceApplicabilityReviewPacketResultReview

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
  SelectedCCFTEmpiricalDiscriminatorBaselineComponentEquationSourceApplicabilityReviewPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  SelectedCCFTEmpiricalDiscriminatorBaselineComponentEquationSourceApplicabilityReviewPacketResultReview.packetId

theorem current_target_points_to_selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_gap_classification_packet :
    currentLiveTarget =
      "prepare_selected_ccft_empirical_discriminator_baseline_component_equation_source_applicability_gap_classification_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
