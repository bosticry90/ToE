import ToeFormal.Derivation.ToeNativePhiSignatureDomainAndPotentialPolicyPacket

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
  ToeNativePhiSignatureDomainAndPotentialPolicyPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativePhiSignatureDomainAndPotentialPolicyPacket.packetId

theorem current_target_points_to_toe_native_phi_variation_retry_under_policy :
    currentLiveTarget =
      "prepare_toe_native_phi_variation_retry_under_selected_policy" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
