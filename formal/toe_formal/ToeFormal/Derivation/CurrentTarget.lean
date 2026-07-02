import ToeFormal.Derivation.PhiTransportTheoremLinkageObligationCloseoutResultReview

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
  PhiTransportTheoremLinkageObligationCloseoutResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  PhiTransportTheoremLinkageObligationCloseoutResultReview.packetId

theorem current_target_points_to_phi_transport_closeout_result_review_selector :
    currentLiveTarget =
      "select_next_ck_family_theorem_linkage_obligation_after_phi_transport_closeout" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
