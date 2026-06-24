import ToeFormal.Derivation.ToeNativeATransportConsistencyCKConstraintCandidatePacketResultReview

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
  ToeNativeATransportConsistencyCKConstraintCandidatePacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeATransportConsistencyCKConstraintCandidatePacketResultReview.packetId

theorem current_target_points_to_a_transport_consistency_functional_embedding :
    currentLiveTarget =
      "prepare_toe_native_A_transport_consistency_ck_functional_embedding_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
