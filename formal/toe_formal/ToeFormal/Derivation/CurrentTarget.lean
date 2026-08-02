import ToeFormal.Derivation.ToeTargetedCCFTClosureContractExtractionResult

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeTargetedCCFTClosureContractExtractionResult

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := selectedNextTarget
def currentEvidencePacketId : String := resultId
def currentBoundedProgramId : String := programId
def currentBoundedProgramState : String := "CLOSED"
def currentTargetPhase : String := "TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_STAGE_2_CLOSED_PASSED"
def currentBoundedAttemptNumber : Nat := attemptSequenceNumber
def lastClosedBoundedSemanticStage : String := semanticStageId
def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_selects_adjudication_without_authorizing_it :
    currentLiveTarget = "adjudicate_toe_targeted_ccft_contract_completeness_and_conflicts_v0" ∧ currentBoundedProgramId = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0" ∧
    currentBoundedProgramState = "CLOSED" ∧ currentBoundedAttemptNumber = 2 ∧
    frozenSourceCount = 96 ∧ contractRecordCount > 0 ∧
    contractAdjudicationPerformed = false ∧ stageThreeAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
