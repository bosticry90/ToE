import ToeFormal.Derivation.SelectedCCFTEmpiricalDiscriminatorResidualFormulaSelectionPacketResultReview

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
  SelectedCCFTEmpiricalDiscriminatorResidualFormulaSelectionPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  SelectedCCFTEmpiricalDiscriminatorResidualFormulaSelectionPacketResultReview.packetId

theorem current_target_points_to_selected_ccft_empirical_discriminator_measurement_feedback_baseline_pressure_packet :
    currentLiveTarget =
      "prepare_selected_ccft_empirical_discriminator_measurement_feedback_baseline_pressure_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
