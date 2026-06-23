import ToeFormal.Derivation.ToeNativeASourceAdmissibilityCKConstraintCandidatePacketResultReview

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
  ToeNativeASourceAdmissibilityCKConstraintCandidatePacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeASourceAdmissibilityCKConstraintCandidatePacketResultReview.packetId

theorem current_target_points_to_a_source_admissibility_ck_functional_embedding :
    currentLiveTarget =
      "prepare_toe_native_A_source_admissibility_ck_functional_embedding_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
