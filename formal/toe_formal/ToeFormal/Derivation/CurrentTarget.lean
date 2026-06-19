import ToeFormal.Derivation.MasterActionCKConstraintFunctionalDefinitionPacket

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
  MasterActionCKConstraintFunctionalDefinitionPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  MasterActionCKConstraintFunctionalDefinitionPacket.packetId

theorem current_target_points_to_master_action_ck_definition_packet_review :
    currentLiveTarget =
      "review_master_action_ck_constraint_functional_definition_packet_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
