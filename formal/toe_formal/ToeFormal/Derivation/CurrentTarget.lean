import ToeFormal.Derivation.MasterActionCKConstraintFamilySelectionForPhiRoute

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
  MasterActionCKConstraintFamilySelectionForPhiRoute.selectedNextTarget

def currentEvidencePacketId : String :=
  MasterActionCKConstraintFamilySelectionForPhiRoute.packetId

theorem current_target_points_to_phi_source_admissibility_ck_candidate_packet :
    currentLiveTarget =
      "prepare_phi_source_admissibility_ck_constraint_candidate_packet" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
