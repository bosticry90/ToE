import ToeFormal.Derivation.CCFTEmpiricalDiscriminatorCandidateMapPacket

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
  CCFTEmpiricalDiscriminatorCandidateMapPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  CCFTEmpiricalDiscriminatorCandidateMapPacket.packetId

theorem current_target_points_to_ccft_empirical_discriminator_candidate_map_review :
    currentLiveTarget =
      "review_ccft_empirical_discriminator_candidate_map_packet_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
