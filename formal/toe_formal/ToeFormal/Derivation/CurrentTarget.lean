import ToeFormal.Derivation.ToeNativeABridgeAdmissibilityCKFunctionalEmbeddingPacket

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
  ToeNativeABridgeAdmissibilityCKFunctionalEmbeddingPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeABridgeAdmissibilityCKFunctionalEmbeddingPacket.packetId

theorem current_target_points_to_a_bridge_functional_embedding_result_review :
    currentLiveTarget =
      "review_toe_native_A_bridge_admissibility_ck_functional_embedding_packet_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
