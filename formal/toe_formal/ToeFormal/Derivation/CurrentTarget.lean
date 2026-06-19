import ToeFormal.Derivation.PhiSourceAdmissibilityCKAdmissibilityRuleCloseout

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
  PhiSourceAdmissibilityCKAdmissibilityRuleCloseout.selectedNextTarget

def currentEvidencePacketId : String :=
  PhiSourceAdmissibilityCKAdmissibilityRuleCloseout.packetId

theorem current_target_points_to_next_phi_relevant_ck_family_selector :
    currentLiveTarget =
      "select_next_phi_relevant_ck_constraint_family_after_source_admissibility" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
