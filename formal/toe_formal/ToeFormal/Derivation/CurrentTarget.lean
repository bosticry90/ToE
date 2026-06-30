import ToeFormal.Derivation.CKFamilyTheoremLinkageObligationSelectionAfterASourceCloseoutResultReview

/-
Thin current-target aggregate for tiered validation. This target follows the
live strict target and avoids requiring a full ToeFormal aggregate build for
routine packet checks.
-/

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

set_option linter.style.longLine false

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  CKFamilyTheoremLinkageObligationSelectionAfterASourceCloseoutResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  CKFamilyTheoremLinkageObligationSelectionAfterASourceCloseoutResultReview.packetId

theorem current_target_points_to_phi_source_packet_after_selector_result_review :
    currentLiveTarget =
      "prepare_phi_source_theorem_linkage_obligation_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
