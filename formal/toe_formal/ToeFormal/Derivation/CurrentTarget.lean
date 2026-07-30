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
  ToeNativeControlledCoherenceClaimInventoryResult.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeControlledCoherenceClaimInventoryResult.reviewId

def currentBoundedProgramId : String :=
  "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0"

def currentBoundedProgramState : String := "CLOSED"

def currentTargetPhase : String :=
  "STAGE_1_CLOSED_PASSED_AWAITING_STAGE_2_OPEN"

def currentBoundedAttemptNumber : Nat := 1

def lastClosedBoundedSemanticStage : String :=
  "CONTROLLED_COHERENCE_CLAIM_INVENTORY"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_selects_unopened_operational_definition_stage :
    currentLiveTarget =
      "test_toe_native_coherence_claim_operational_definition_v0" := by
  rfl

theorem controlled_coherence_claim_inventory_is_closed_passed :
    currentBoundedProgramId =
      "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0" ∧
    currentBoundedProgramState = "CLOSED" ∧
    currentTargetPhase =
      "STAGE_1_CLOSED_PASSED_AWAITING_STAGE_2_OPEN" ∧
    currentBoundedAttemptNumber = 1 ∧
    lastClosedBoundedSemanticStage =
      "CONTROLLED_COHERENCE_CLAIM_INVENTORY" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    ToeNativeControlledCoherenceClaimInventoryResult.stageTwoOpened =
      false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
