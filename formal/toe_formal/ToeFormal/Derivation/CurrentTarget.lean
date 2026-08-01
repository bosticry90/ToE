import ToeFormal.Derivation.ToeMinimalClosedCCFTCoreDecisionAttemptOpen

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String :=
  ToeMinimalClosedCCFTCoreDecisionAttemptOpen.target
def currentEvidencePacketId : String :=
  "TOE_MINIMAL_CLOSED_CCFT_CORE_DECISION_OPEN_VALIDATION_v0"
def currentBoundedProgramId : String :=
  ToeMinimalClosedCCFTCoreDecisionAttemptOpen.programId
def currentBoundedProgramState : String := "OPEN"
def currentTargetPhase : String :=
  "STAGE_4_OPEN_NO_SCIENTIFIC_RESULT"
def currentBoundedAttemptNumber : Nat :=
  ToeMinimalClosedCCFTCoreDecisionAttemptOpen.attemptSequenceNumber
def lastClosedBoundedSemanticStage : String :=
  "CCFT_MATHEMATICAL_OBJECT_OPERATIONALIZATION"
def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_opens_minimal_ccft_surrogate_core_decision :
    currentLiveTarget = "select_or_reject_toe_minimal_closed_ccft_core_v0" := by
  rfl

theorem minimal_ccft_surrogate_core_decision_is_open_without_result :
    currentBoundedProgramId =
      "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_V0" ∧
    currentBoundedProgramState = "OPEN" ∧
    currentTargetPhase = "STAGE_4_OPEN_NO_SCIENTIFIC_RESULT" ∧
    currentBoundedAttemptNumber = 4 ∧
    lastClosedBoundedSemanticStage =
      "CCFT_MATHEMATICAL_OBJECT_OPERATIONALIZATION" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    ToeMinimalClosedCCFTCoreDecisionAttemptOpen.operationalRecordCount = 20 ∧
    ToeMinimalClosedCCFTCoreDecisionAttemptOpen.boundedSurrogateRecordCount = 5 ∧
    ToeMinimalClosedCCFTCoreDecisionAttemptOpen.fullyPhysicallyOperationalObjectCount = 0 ∧
    ToeMinimalClosedCCFTCoreDecisionAttemptOpen.candidateCoreRowsEvaluatedAtOpen = 0 ∧
    ToeMinimalClosedCCFTCoreDecisionAttemptOpen.closureMatrixCellsPopulatedAtOpen = 0 ∧
    ToeMinimalClosedCCFTCoreDecisionAttemptOpen.minimalCoreSelected = false ∧
    ToeMinimalClosedCCFTCoreDecisionAttemptOpen.physicalCCFTModelEstablished = false ∧
    ToeMinimalClosedCCFTCoreDecisionAttemptOpen.stageFiveAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
