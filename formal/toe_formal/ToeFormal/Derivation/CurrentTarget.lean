import ToeFormal.Derivation.ToeNativeAVacuumVariationRetryUnderSelectedU1PolicyPacket

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
  ToeNativeAVacuumVariationRetryUnderSelectedU1PolicyPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeAVacuumVariationRetryUnderSelectedU1PolicyPacket.packetId

theorem current_target_points_to_a_vacuum_u1_variation_retry_result_review :
    currentLiveTarget =
      "review_toe_native_A_vacuum_variation_retry_under_selected_u1_policy_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
