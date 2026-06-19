import ToeFormal.Derivation.PhiTransportConsistencyCKConstraintCandidatePacketResultReview

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
  PhiTransportConsistencyCKConstraintCandidatePacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  PhiTransportConsistencyCKConstraintCandidatePacketResultReview.packetId

theorem current_target_points_to_phi_transport_consistency_functional_embedding_packet :
    currentLiveTarget =
      "prepare_phi_transport_consistency_ck_functional_embedding_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
