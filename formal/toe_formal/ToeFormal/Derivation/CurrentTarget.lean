import ToeFormal.Derivation.MasterActionCKConstraintFunctionalDefinitionPacketResultReview

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
  MasterActionCKConstraintFunctionalDefinitionPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  MasterActionCKConstraintFunctionalDefinitionPacketResultReview.packetId

theorem current_target_points_to_master_action_ck_constraint_family_selector :
    currentLiveTarget =
      "select_master_action_ck_constraint_family_for_phi_route" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
