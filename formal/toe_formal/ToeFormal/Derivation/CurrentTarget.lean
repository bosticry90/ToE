import ToeFormal.Derivation.ToeNativePhiSurfaceAlignmentWitnessCloseout

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
  ToeNativePhiSurfaceAlignmentWitnessCloseout.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativePhiSurfaceAlignmentWitnessCloseout.packetId

theorem current_target_points_to_toe_native_phi_ck_variational_content_packet :
    currentLiveTarget =
      "prepare_toe_native_phi_ck_variational_content_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
