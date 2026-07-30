import ToeFormal.Derivation.ToeNativeCoherenceOperationalDefinitionResult

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
  ToeNativeCoherenceOperationalDefinitionResult.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeCoherenceOperationalDefinitionResult.reviewId

def currentBoundedProgramId : String :=
  "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0"

def currentBoundedProgramState : String := "CLOSED"

def currentTargetPhase : String :=
  "STAGE_2_CLOSED_BLOCKED_AWAITING_MANDATORY_EXIT"

def currentBoundedAttemptNumber : Nat := 2

def lastClosedBoundedSemanticStage : String :=
  "COHERENCE_OPERATIONAL_DEFINITION_TEST"

def lastBoundedTerminalResult : String := "BLOCKED"

theorem current_target_selects_mandatory_bounded_exit :
    currentLiveTarget =
      "close_toe_native_coherence_ontology_and_representation_v0_after_bounded_result_v0" := by
  rfl

theorem operational_definition_stage_is_closed_and_blocked :
    currentBoundedProgramId =
      "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0" ∧
    currentBoundedProgramState = "CLOSED" ∧
    currentTargetPhase =
      "STAGE_2_CLOSED_BLOCKED_AWAITING_MANDATORY_EXIT" ∧
    currentBoundedAttemptNumber = 2 ∧
    lastClosedBoundedSemanticStage =
      "COHERENCE_OPERATIONAL_DEFINITION_TEST" ∧
    lastBoundedTerminalResult = "BLOCKED" ∧
    ToeNativeCoherenceOperationalDefinitionResult.stageThreeMayOpen =
      false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
