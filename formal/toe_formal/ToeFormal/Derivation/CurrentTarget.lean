import ToeFormal.Derivation.ToeNativeATransportConsistencyCKConstraintCandidatePacket

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
  ToeNativeATransportConsistencyCKConstraintCandidatePacket.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeATransportConsistencyCKConstraintCandidatePacket.packetId

theorem current_target_points_to_a_transport_consistency_candidate_review :
    currentLiveTarget =
      "review_toe_native_A_transport_consistency_ck_constraint_candidate_packet_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
