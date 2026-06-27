import ToeFormal.Derivation.MasterActionCKFamilyGapReviewAfterPhiAAndPsiA

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
  MasterActionCKFamilyGapReviewAfterPhiAAndPsiA.selectedNextTarget

def currentEvidencePacketId : String :=
  MasterActionCKFamilyGapReviewAfterPhiAAndPsiA.packetId

theorem current_target_points_to_master_action_ck_family_gap_review_result_after_phi_A_and_psi_A :
    currentLiveTarget =
      "review_master_action_ck_family_gap_review_after_phi_A_and_psi_A_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
