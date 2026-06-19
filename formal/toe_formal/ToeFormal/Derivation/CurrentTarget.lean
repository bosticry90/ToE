import ToeFormal.Derivation.PhiTransportConsistencyCKConstraintCandidatePacket

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
  PhiTransportConsistencyCKConstraintCandidatePacket.selectedNextTarget

def currentEvidencePacketId : String :=
  PhiTransportConsistencyCKConstraintCandidatePacket.packetId

theorem current_target_points_to_phi_transport_consistency_candidate_packet_review :
    currentLiveTarget =
      "review_phi_transport_consistency_ck_constraint_candidate_packet_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
