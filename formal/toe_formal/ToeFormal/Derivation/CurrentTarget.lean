import ToeFormal.Derivation.PhiCKAdmissibilityRuleFamilySynthesisCloseout

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
  PhiCKAdmissibilityRuleFamilySynthesisCloseout.selectedNextTarget

def currentEvidencePacketId : String :=
  PhiCKAdmissibilityRuleFamilySynthesisCloseout.packetId

theorem current_target_points_to_next_ck_constraint_family_selector :
    currentLiveTarget =
      "select_next_ck_constraint_family_after_phi_source_and_bridge_admissibility" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
