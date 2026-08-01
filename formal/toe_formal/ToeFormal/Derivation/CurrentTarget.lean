import ToeFormal.Derivation.ToeMinimalClosedCCFTCoreDecisionResult

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String :=
  ToeMinimalClosedCCFTCoreDecisionResult.selectedNextTarget
def currentEvidencePacketId : String :=
  ToeMinimalClosedCCFTCoreDecisionResult.reviewId
def currentBoundedProgramId : String :=
  ToeMinimalClosedCCFTCoreDecisionResult.programId
def currentBoundedProgramState : String := "CLOSED"
def currentTargetPhase : String :=
  "STAGE_4_CLOSED_BLOCKED_AWAITING_MANDATORY_EXIT"
def currentBoundedAttemptNumber : Nat :=
  ToeMinimalClosedCCFTCoreDecisionResult.attemptSequenceNumber
def lastClosedBoundedSemanticStage : String :=
  "CCFT_MATHEMATICAL_OBJECT_OPERATIONALIZATION"
def lastBoundedTerminalResult : String := "BLOCKED"

theorem current_target_selects_mandatory_ccft_core_program_exit :
    currentLiveTarget =
      "close_toe_ccft_native_mathematical_core_and_operationalization_v0_after_bounded_result_v0" := by
  rfl

theorem minimal_ccft_surrogate_core_decision_is_closed_and_blocked :
    currentBoundedProgramId =
      "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_V0" ∧
    currentBoundedProgramState = "CLOSED" ∧
    currentTargetPhase = "STAGE_4_CLOSED_BLOCKED_AWAITING_MANDATORY_EXIT" ∧
    currentBoundedAttemptNumber = 4 ∧
    lastClosedBoundedSemanticStage =
      "CCFT_MATHEMATICAL_OBJECT_OPERATIONALIZATION" ∧
    lastBoundedTerminalResult = "BLOCKED" ∧
    ToeMinimalClosedCCFTCoreDecisionResult.candidateCount = 2 ∧
    ToeMinimalClosedCCFTCoreDecisionResult.closureCellCount = 24 ∧
    ToeMinimalClosedCCFTCoreDecisionResult.minimalCoreSelected = false ∧
    ToeMinimalClosedCCFTCoreDecisionResult.physicalCCFTModelEstablished = false ∧
    ToeMinimalClosedCCFTCoreDecisionResult.stageBlocked = true ∧
    ToeMinimalClosedCCFTCoreDecisionResult.mandatoryExitCompleted = false ∧
    ToeMinimalClosedCCFTCoreDecisionResult.stageFiveAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
