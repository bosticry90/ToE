import ToeFormal.Derivation.ToeNativePhiVariationRetryUnderSelectedPolicyResultReview

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
  ToeNativePhiVariationRetryUnderSelectedPolicyResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativePhiVariationRetryUnderSelectedPolicyResultReview.packetId

theorem current_target_points_to_toe_native_phi_alignment_witness_closeout :
    currentLiveTarget =
      "prepare_toe_native_phi_surface_alignment_witness_closeout" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
