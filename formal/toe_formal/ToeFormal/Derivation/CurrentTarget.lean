import ToeFormal.Derivation.PhiBridgeTheoremLinkageAttemptFromStandalonePhiBridgeRouteExecution

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
  PhiBridgeTheoremLinkageAttemptFromStandalonePhiBridgeRouteExecution.selectedNextTarget

def currentEvidencePacketId : String :=
  PhiBridgeTheoremLinkageAttemptFromStandalonePhiBridgeRouteExecution.packetId

theorem current_target_points_to_phi_bridge_attempt_execution_result_review :
    currentLiveTarget =
      "review_phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_execution_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
