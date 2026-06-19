import ToeFormal.Derivation.PhiBridgeAdmissibilityCKFunctionalEmbeddingPacketResultReview

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
  PhiBridgeAdmissibilityCKFunctionalEmbeddingPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  PhiBridgeAdmissibilityCKFunctionalEmbeddingPacketResultReview.packetId

theorem current_target_points_to_phi_bridge_admissibility_rule_closeout :
    currentLiveTarget =
      "prepare_phi_bridge_admissibility_ck_admissibility_rule_closeout" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
