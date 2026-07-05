import ToeFormal.Derivation.SelectedCCFTEmpiricalDiscriminatorBaselineComponentEquationSourceCandidateRegistryPacket

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
  SelectedCCFTEmpiricalDiscriminatorBaselineComponentEquationSourceCandidateRegistryPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  SelectedCCFTEmpiricalDiscriminatorBaselineComponentEquationSourceCandidateRegistryPacket.packetId

theorem current_target_points_to_selected_ccft_empirical_discriminator_baseline_component_equation_source_candidate_registry_packet_result_review :
    currentLiveTarget =
      "review_selected_ccft_empirical_discriminator_baseline_component_equation_source_candidate_registry_packet_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
