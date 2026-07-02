import ToeFormal.Derivation.PhiTransportTheoremLinkageAttemptFromStandalonePhiTransportRouteExecutionResultReview

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
  PhiTransportTheoremLinkageAttemptFromStandalonePhiTransportRouteExecutionResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  PhiTransportTheoremLinkageAttemptFromStandalonePhiTransportRouteExecutionResultReview.packetId

theorem current_target_points_to_phi_transport_obligation_closeout_preparation :
    currentLiveTarget =
      "prepare_phi_transport_theorem_linkage_obligation_closeout" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
