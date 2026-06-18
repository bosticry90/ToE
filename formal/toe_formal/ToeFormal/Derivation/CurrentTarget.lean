import ToeFormal.Derivation.QFTGRSourceAdmissibilityReviewForProvisionalScalarSource

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
  QFTGRSourceAdmissibilityReviewForProvisionalScalarSource.selectedNextTarget

def currentEvidencePacketId : String :=
  QFTGRSourceAdmissibilityReviewForProvisionalScalarSource.packetId

theorem current_target_points_to_scoped_semiclassical_gate_review :
    currentLiveTarget =
      "prepare_qft_gr_semiclassical_coupling_gate_scope_review_for_provisional_" ++
        "scalar_source" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
