import ToeFormal.Derivation.CCFTCKAdmissibilityObligationIndexPacketResultReview

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
  CCFTCKAdmissibilityObligationIndexPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  CCFTCKAdmissibilityObligationIndexPacketResultReview.packetId

theorem current_target_points_to_ccft_full_variational_action_program_packet :
    currentLiveTarget =
      "prepare_ccft_full_variational_action_program_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
