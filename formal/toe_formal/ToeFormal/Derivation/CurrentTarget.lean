import ToeFormal.Derivation.CKFamilyTheoremLinkageObligationIndex

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
  CKFamilyTheoremLinkageObligationIndex.selectedNextTarget

def currentEvidencePacketId : String :=
  CKFamilyTheoremLinkageObligationIndex.packetId

theorem current_target_points_to_theorem_linkage_obligation_index_result_review :
    currentLiveTarget =
      "review_ck_family_theorem_linkage_obligation_index_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
