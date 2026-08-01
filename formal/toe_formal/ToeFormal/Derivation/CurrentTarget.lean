import ToeFormal.Derivation.ToeCCFTMathematicalObjectOperationalizationResult

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String :=
  ToeCCFTMathematicalObjectOperationalizationResult.selectedNextTarget
def currentEvidencePacketId : String :=
  ToeCCFTMathematicalObjectOperationalizationResult.reviewId
def currentBoundedProgramId : String :=
  ToeCCFTMathematicalObjectOperationalizationResult.programId
def currentBoundedProgramState : String := "CLOSED"
def currentTargetPhase : String :=
  "STAGE_3_CLOSED_PASSED_BOUNDED_SURROGATES_AWAITING_SEPARATE_STAGE_4_AUTHORITY"
def currentBoundedAttemptNumber : Nat :=
  ToeCCFTMathematicalObjectOperationalizationResult.attemptSequenceNumber
def lastClosedBoundedSemanticStage : String :=
  "CCFT_MATHEMATICAL_OBJECT_OPERATIONALIZATION"
def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_selects_unopened_minimal_ccft_core_decision :
    currentLiveTarget = "select_or_reject_toe_minimal_closed_ccft_core_v0" := by
  rfl

theorem ccft_object_operationalization_is_closed_with_surrogates_only :
    currentBoundedProgramId =
      "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_V0" ∧
    currentBoundedProgramState = "CLOSED" ∧
    currentTargetPhase =
      "STAGE_3_CLOSED_PASSED_BOUNDED_SURROGATES_AWAITING_SEPARATE_STAGE_4_AUTHORITY" ∧
    currentBoundedAttemptNumber = 3 ∧
    lastBoundedTerminalResult = "PASSED" ∧
    ToeCCFTMathematicalObjectOperationalizationResult.operationalRecordCount = 20 ∧
    ToeCCFTMathematicalObjectOperationalizationResult.fullyPhysicallyOperationalObjectCount = 0 ∧
    ToeCCFTMathematicalObjectOperationalizationResult.boundedSurrogateRecordCount = 5 ∧
    ToeCCFTMathematicalObjectOperationalizationResult.genericWaveBaselineIdentified = true ∧
    ToeCCFTMathematicalObjectOperationalizationResult.preferredFormulationSelected = false ∧
    ToeCCFTMathematicalObjectOperationalizationResult.minimalCoreSelected = false ∧
    ToeCCFTMathematicalObjectOperationalizationResult.stageFourAuthorized = false ∧
    ToeCCFTMathematicalObjectOperationalizationResult.stageFourOpened = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
