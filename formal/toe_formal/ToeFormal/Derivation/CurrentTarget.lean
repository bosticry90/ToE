import ToeFormal.Derivation.ASourceTheoremLinkageObligationPacket

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
  ASourceTheoremLinkageObligationPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  ASourceTheoremLinkageObligationPacket.packetId

theorem current_target_points_to_A_source_theorem_linkage_obligation_packet_review :
    currentLiveTarget =
      "review_A_source_theorem_linkage_obligation_packet_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
