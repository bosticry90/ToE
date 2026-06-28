import ToeFormal.Derivation.PsiAMatterSectorExchangeTheoremLinkageObligationPacket

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
  PsiAMatterSectorExchangeTheoremLinkageObligationPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  PsiAMatterSectorExchangeTheoremLinkageObligationPacket.packetId

theorem current_target_points_to_psi_A_matter_exchange_obligation_packet_review :
    currentLiveTarget =
      "review_psi_A_matter_sector_exchange_theorem_linkage_obligation_packet_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
