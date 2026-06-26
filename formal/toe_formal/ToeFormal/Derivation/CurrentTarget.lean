import ToeFormal.Derivation.ToeNativePsiAU1CExchangeFunctionalEmbeddingPacketResultReview

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
  ToeNativePsiAU1CExchangeFunctionalEmbeddingPacketResultReview.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativePsiAU1CExchangeFunctionalEmbeddingPacketResultReview.packetId

theorem current_target_points_to_psi_a_u1_cexchange_admissibility_rule_closeout :
    currentLiveTarget =
      "prepare_toe_native_psi_A_u1_cexchange_admissibility_rule_closeout" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
