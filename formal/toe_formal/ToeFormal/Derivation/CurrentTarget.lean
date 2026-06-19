import ToeFormal.Derivation.PhiBridgeAdmissibilityCKConstraintCandidatePacketResultReview

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
  PhiBridgeAdmissibilityCKConstraintCandidatePacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  PhiBridgeAdmissibilityCKConstraintCandidatePacketResultReview.packetId

theorem current_target_points_to_phi_bridge_admissibility_functional_embedding :
    currentLiveTarget =
      "prepare_phi_bridge_admissibility_ck_functional_embedding_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
