import ToeFormal.Derivation.ToeNativePsiAU1CExchangeConstraintCandidatePacket

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
  ToeNativePsiAU1CExchangeConstraintCandidatePacket.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativePsiAU1CExchangeConstraintCandidatePacket.packetId

theorem current_target_points_to_psi_a_u1_cexchange_constraint_candidate_packet_result_review :
    currentLiveTarget =
      "review_toe_native_psi_A_u1_cexchange_constraint_candidate_packet_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
