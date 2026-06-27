import ToeFormal.Derivation.CKFamilyTopTheoremLinkageObligationPacket

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
  CKFamilyTopTheoremLinkageObligationPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  CKFamilyTopTheoremLinkageObligationPacket.packetId

theorem current_target_points_to_ck_family_top_theorem_linkage_obligation_packet_review :
    currentLiveTarget =
      "review_ck_family_top_theorem_linkage_obligation_packet_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
