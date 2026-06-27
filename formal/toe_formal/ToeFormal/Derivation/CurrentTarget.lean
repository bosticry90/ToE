import ToeFormal.Derivation.CKFamilyTheoremLinkagePrioritySelectionAfterIndexResultReview

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
  CKFamilyTheoremLinkagePrioritySelectionAfterIndexResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  CKFamilyTheoremLinkagePrioritySelectionAfterIndexResultReview.packetId

theorem current_target_points_to_ck_family_top_theorem_linkage_obligation_packet :
    currentLiveTarget =
      "prepare_ck_family_top_theorem_linkage_obligation_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
