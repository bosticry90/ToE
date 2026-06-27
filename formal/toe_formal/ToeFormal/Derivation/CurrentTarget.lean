import ToeFormal.Derivation.CKFamilyTheoremLinkageObligationSelectionAfterIndexResultReview

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
  CKFamilyTheoremLinkageObligationSelectionAfterIndexResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  CKFamilyTheoremLinkageObligationSelectionAfterIndexResultReview.packetId

theorem current_target_points_to_theorem_linkage_priority_selection_preparation :
    currentLiveTarget =
      "prepare_ck_family_theorem_linkage_priority_selection_after_index" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
