import ToeFormal.Derivation.ToeNativeASourceAdmissibilityCKFunctionalEmbeddingPacketResultReview

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
  ToeNativeASourceAdmissibilityCKFunctionalEmbeddingPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeASourceAdmissibilityCKFunctionalEmbeddingPacketResultReview.packetId

theorem current_target_points_to_a_source_admissibility_ck_rule_closeout :
    currentLiveTarget =
      "prepare_toe_native_A_source_admissibility_ck_admissibility_rule_closeout" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
