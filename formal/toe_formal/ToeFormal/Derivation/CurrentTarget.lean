import ToeFormal.Derivation.ToeNativeASourceAdmissibilityCKAdmissibilityRuleCloseout

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
  ToeNativeASourceAdmissibilityCKAdmissibilityRuleCloseout.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeASourceAdmissibilityCKAdmissibilityRuleCloseout.packetId

theorem current_target_points_to_a_ck_family_selector_after_source_admissibility :
    currentLiveTarget =
      "select_next_toe_native_A_ck_constraint_family_after_source_admissibility" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
