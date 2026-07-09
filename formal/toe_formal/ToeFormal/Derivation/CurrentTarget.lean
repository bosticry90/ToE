import ToeFormal.Derivation.CCFTSCQEDLiteratureApplicabilityMatrixCalculationResultReview

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
  CCFTSCQEDLiteratureApplicabilityMatrixCalculationResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  CCFTSCQEDLiteratureApplicabilityMatrixCalculationResultReview.reviewId

theorem current_target_points_to_science_first_pillar_seam_dependency_rebase :
    currentLiveTarget =
      "prepare_science_first_pillar_seam_dependency_rebase_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
