import ToeFormal.Derivation.ToeNativeABridgeAdmissibilityCKConstraintCandidatePacket

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
  ToeNativeABridgeAdmissibilityCKConstraintCandidatePacket.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeABridgeAdmissibilityCKConstraintCandidatePacket.packetId

theorem current_target_points_to_a_bridge_candidate_review_after_packet :
    currentLiveTarget =
      "review_toe_native_A_bridge_admissibility_ck_constraint_candidate_packet_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
