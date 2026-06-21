import ToeFormal.Derivation.ToeNativeAGaugeGroupDomainAndCurrentPolicyPacket

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
  ToeNativeAGaugeGroupDomainAndCurrentPolicyPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeAGaugeGroupDomainAndCurrentPolicyPacket.packetId

theorem current_target_points_to_a_vacuum_u1_variation_retry_packet :
    currentLiveTarget =
      "prepare_toe_native_A_vacuum_variation_retry_under_selected_u1_policy" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
