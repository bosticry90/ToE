import ToeFormal.Derivation.PhiTransportTheoremLinkageObligationPacket

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
  PhiTransportTheoremLinkageObligationPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  PhiTransportTheoremLinkageObligationPacket.packetId

theorem current_target_points_to_phi_transport_obligation_packet_review :
    currentLiveTarget =
      "review_phi_transport_theorem_linkage_obligation_packet_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
