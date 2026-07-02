import ToeFormal.Derivation.PhiTransportTheoremLinkageObligationPacketResultReview

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
  PhiTransportTheoremLinkageObligationPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  PhiTransportTheoremLinkageObligationPacketResultReview.packetId

theorem current_target_points_to_phi_transport_attempt_preparation :
    currentLiveTarget =
      "prepare_phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
