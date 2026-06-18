import ToeFormal.Derivation.QFTGRSemiclassicalCouplingGateScopeReviewForProvisionalScalarSource

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
  QFTGRSemiclassicalCouplingGateScopeReviewForProvisionalScalarSource.selectedNextTarget

def currentEvidencePacketId : String :=
  QFTGRSemiclassicalCouplingGateScopeReviewForProvisionalScalarSource.packetId

theorem current_target_points_to_classical_einstein_scalar_route_packet :
    currentLiveTarget =
      "prepare_qft_gr_classical_einstein_scalar_coupling_route_packet_for_" ++
        "provisional_scalar_source" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
