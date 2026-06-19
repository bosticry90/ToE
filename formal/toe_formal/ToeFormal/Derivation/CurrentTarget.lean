import ToeFormal.Derivation.PhiBridgeAdmissibilityCKConstraintCandidatePacket

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
  PhiBridgeAdmissibilityCKConstraintCandidatePacket.selectedNextTarget

def currentEvidencePacketId : String :=
  PhiBridgeAdmissibilityCKConstraintCandidatePacket.packetId

theorem current_target_points_to_phi_bridge_admissibility_candidate_review :
    currentLiveTarget =
      "review_phi_bridge_admissibility_ck_constraint_candidate_packet_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
