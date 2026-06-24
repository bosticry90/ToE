import ToeFormal.Derivation.ToeNativeATransportConsistencyCKFunctionalEmbeddingPacketResultReview

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
  ToeNativeATransportConsistencyCKFunctionalEmbeddingPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeATransportConsistencyCKFunctionalEmbeddingPacketResultReview.packetId

theorem current_target_points_to_a_transport_consistency_admissibility_rule_closeout :
    currentLiveTarget =
      "prepare_toe_native_A_transport_consistency_ck_admissibility_rule_closeout" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
