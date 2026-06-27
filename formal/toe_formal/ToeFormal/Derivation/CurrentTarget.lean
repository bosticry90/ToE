import ToeFormal.Derivation.MasterActionCKFamilyStatusSynthesisAfterPhiAAndPsiA

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
  MasterActionCKFamilyStatusSynthesisAfterPhiAAndPsiA.selectedNextTarget

def currentEvidencePacketId : String :=
  MasterActionCKFamilyStatusSynthesisAfterPhiAAndPsiA.packetId

theorem current_target_points_to_master_action_ck_family_status_synthesis_after_phi_A_and_psi_A_result_review :
    currentLiveTarget =
      "review_master_action_ck_family_status_synthesis_after_phi_A_and_psi_A_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
