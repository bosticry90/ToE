import ToeFormal.Derivation.QFTGRClassicalEinsteinScalarCouplingRoutePacketResultReview

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
  QFTGRClassicalEinsteinScalarCouplingRoutePacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  QFTGRClassicalEinsteinScalarCouplingRoutePacketResultReview.packetId

theorem current_target_points_to_classical_einstein_scalar_route_witness_closeout :
    currentLiveTarget =
      "prepare_qft_gr_provisional_scalar_classical_source_route_witness_closeout" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
