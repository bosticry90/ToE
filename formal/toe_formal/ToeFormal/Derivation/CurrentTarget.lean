import ToeFormal.Derivation.ToeNativeControlledCoherenceClaimInventoryAttemptOpen

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
  "inventory_toe_native_controlled_coherence_claims_v0"

def currentEvidencePacketId : String :=
  ToeNativeControlledCoherenceClaimInventoryAttemptOpen.evidenceId

def currentBoundedProgramId : String :=
  "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0"

def currentBoundedProgramState : String := "OPEN"

def currentTargetPhase : String :=
  "STAGE_1_OPEN_AWAITING_CONTROLLED_CLAIM_INVENTORY"

def currentBoundedAttemptNumber : Nat := 1

def lastClosedBoundedSemanticStage : String :=
  "NONE_IN_CURRENT_PROGRAM"

def lastBoundedTerminalResult : String := "NONE_IN_CURRENT_PROGRAM"

theorem current_target_opens_controlled_coherence_claim_inventory :
    currentLiveTarget =
      "inventory_toe_native_controlled_coherence_claims_v0" := by
  rfl

theorem controlled_coherence_claim_inventory_is_open_without_stage_output :
    currentBoundedProgramId =
      "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0" ∧
    currentBoundedProgramState = "OPEN" ∧
    currentTargetPhase =
      "STAGE_1_OPEN_AWAITING_CONTROLLED_CLAIM_INVENTORY" ∧
    currentBoundedAttemptNumber = 1 ∧
    lastClosedBoundedSemanticStage = "NONE_IN_CURRENT_PROGRAM" ∧
    lastBoundedTerminalResult = "NONE_IN_CURRENT_PROGRAM" ∧
    ToeNativeControlledCoherenceClaimInventoryAttemptOpen.scientificOutputPresent =
      false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
