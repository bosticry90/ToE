import ToeFormal.Derivation.PhiSourceTheoremLinkageObligationCloseout

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
  PhiSourceTheoremLinkageObligationCloseout.selectedNextTarget

def currentEvidencePacketId : String :=
  PhiSourceTheoremLinkageObligationCloseout.packetId

theorem current_target_points_to_phi_source_obligation_closeout_result_review :
    currentLiveTarget =
      "review_phi_source_theorem_linkage_obligation_closeout_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
