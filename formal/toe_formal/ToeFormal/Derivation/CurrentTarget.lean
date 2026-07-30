import ToeFormal.Derivation.ToeNativeCoherenceOperationalDefinitionAttemptOpen
import ToeFormal.Derivation.ToeNativeControlledCoherenceClaimInventoryResult

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
  ToeNativeCoherenceOperationalDefinitionAttemptOpen.target

def currentEvidencePacketId : String :=
  ToeNativeControlledCoherenceClaimInventoryResult.reviewId

def currentBoundedProgramId : String :=
  "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0"

def currentBoundedProgramState : String := "OPEN"

def currentTargetPhase : String :=
  "STAGE_2_OPEN_AWAITING_OPERATIONAL_DEFINITION_RESULT"

def currentBoundedAttemptNumber : Nat := 2

def currentBoundedSemanticStage : String :=
  "COHERENCE_OPERATIONAL_DEFINITION_TEST"

def lastClosedBoundedSemanticStage : String :=
  "CONTROLLED_COHERENCE_CLAIM_INVENTORY"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_opens_operational_definition_stage :
    currentLiveTarget =
      "test_toe_native_coherence_claim_operational_definition_v0" := by
  rfl

theorem operational_definition_stage_is_open_after_inventory_close :
    currentBoundedProgramId =
      "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0" ∧
    currentBoundedProgramState = "OPEN" ∧
    currentTargetPhase =
      "STAGE_2_OPEN_AWAITING_OPERATIONAL_DEFINITION_RESULT" ∧
    currentBoundedAttemptNumber = 2 ∧
    currentBoundedSemanticStage =
      "COHERENCE_OPERATIONAL_DEFINITION_TEST" ∧
    lastClosedBoundedSemanticStage =
      "CONTROLLED_COHERENCE_CLAIM_INVENTORY" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    ToeNativeCoherenceOperationalDefinitionAttemptOpen.scientificOutputPresent =
      false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
