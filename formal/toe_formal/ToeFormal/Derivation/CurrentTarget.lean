import ToeFormal.Derivation.CKFamilyTheoremLinkageObligationIndexResultReview

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
  CKFamilyTheoremLinkageObligationIndexResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  CKFamilyTheoremLinkageObligationIndexResultReview.packetId

theorem current_target_points_to_theorem_linkage_obligation_after_index_selector :
    currentLiveTarget =
      "select_next_ck_family_theorem_linkage_obligation_after_index" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
