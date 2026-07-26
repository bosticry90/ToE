import ToeFormal.Derivation.CrossPillarClosureFrontier

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
  CrossPillarClosureFrontier.currentLiveNextStrictTargetV0

def currentEvidencePacketId : String :=
  CrossPillarClosureFrontier.currentLiveNextStrictTargetEvidenceV0

theorem current_target_is_nonexecuting_after_v2_nonenrollment :
    currentLiveTarget =
      "await_fresh_response_selector_after_v2_nonenrollment_v0" := by
  rfl

theorem current_evidence_is_v2_nonenrollment_decision :
    currentEvidencePacketId =
      "formal/docs/release/V2_ENROLLMENT_DECISION_20260725_v0.json" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
