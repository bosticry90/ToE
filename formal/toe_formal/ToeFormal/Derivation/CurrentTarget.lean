import ToeFormal.Derivation.PhiSourceTheoremLinkageAttemptFromStandalonePhiRoute

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
  PhiSourceTheoremLinkageAttemptFromStandalonePhiRoute.selectedNextTarget

def currentEvidencePacketId : String :=
  PhiSourceTheoremLinkageAttemptFromStandalonePhiRoute.packetId

theorem current_target_points_to_phi_source_attempt_result_review :
    currentLiveTarget =
      "review_phi_source_theorem_linkage_attempt_from_standalone_phi_route_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
