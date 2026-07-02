import ToeFormal.Derivation.CCFTFullVariationalActionProgramPacketResultReview

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
  CCFTFullVariationalActionProgramPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  CCFTFullVariationalActionProgramPacketResultReview.packetId

theorem current_target_points_to_ccft_empirical_discriminator_candidate_map_packet :
    currentLiveTarget =
      "prepare_ccft_empirical_discriminator_candidate_map_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
