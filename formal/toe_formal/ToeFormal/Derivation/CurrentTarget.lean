import ToeFormal.Derivation.QFTGRClassicalEinsteinScalarCouplingRoutePacketForProvisionalScalarSource

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
  QFTGRClassicalEinsteinScalarCouplingRoutePacketForProvisionalScalarSource.selectedNextTarget

def currentEvidencePacketId : String :=
  QFTGRClassicalEinsteinScalarCouplingRoutePacketForProvisionalScalarSource.packetId

theorem current_target_points_to_classical_einstein_scalar_route_result_review :
    currentLiveTarget =
      "review_qft_gr_classical_einstein_scalar_coupling_route_packet_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
