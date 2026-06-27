import ToeFormal.Derivation.MasterActionCKFamilyStatusSynthesisAfterPhiAAndPsiAResultReview

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
  MasterActionCKFamilyStatusSynthesisAfterPhiAAndPsiAResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  MasterActionCKFamilyStatusSynthesisAfterPhiAAndPsiAResultReview.packetId

theorem current_target_points_to_master_action_surface_selection_after_ck_family_status_synthesis :
    currentLiveTarget =
      "select_next_master_action_surface_after_ck_family_status_synthesis" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
