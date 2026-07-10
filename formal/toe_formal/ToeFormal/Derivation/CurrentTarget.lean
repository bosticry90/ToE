import ToeFormal.Derivation.ScienceFirstPillarSeamDependencyRebasePacketResultReview

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
  ScienceFirstPillarSeamDependencyRebasePacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  ScienceFirstPillarSeamDependencyRebasePacketResultReview.reviewId

theorem current_target_points_to_flat_limit_pretest_guardrail :
    currentLiveTarget =
      "prepare_scalar_qft_gr_source_contract_flat_limit_pretest_guardrail_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
