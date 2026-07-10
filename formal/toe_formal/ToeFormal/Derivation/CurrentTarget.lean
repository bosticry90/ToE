import ToeFormal.Derivation.ScienceFirstPillarSeamDependencyRebasePacket

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
  ScienceFirstPillarSeamDependencyRebasePacket.selectedNextTarget

def currentEvidencePacketId : String :=
  ScienceFirstPillarSeamDependencyRebasePacket.packetId

theorem current_target_points_to_science_first_rebase_result_review :
    currentLiveTarget =
      "review_science_first_pillar_seam_dependency_rebase_packet_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
