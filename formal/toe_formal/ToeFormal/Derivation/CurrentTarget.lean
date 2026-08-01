import ToeFormal.Derivation.ToeTargetedCCFTClosureSourceDiscoveryResult

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeTargetedCCFTClosureSourceDiscoveryResult

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := selectedNextTarget
def currentEvidencePacketId : String := resultId
def currentBoundedProgramId : String := programId
def currentBoundedProgramState : String := "CLOSED"
def currentTargetPhase : String :=
  "TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_STAGE_1_CLOSED_PASSED"
def currentBoundedAttemptNumber : Nat := attemptSequenceNumber
def lastClosedBoundedSemanticStage : String := semanticStageId
def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_selects_contract_extraction_without_authorizing_it :
    currentLiveTarget = "extract_toe_targeted_ccft_closure_contracts_v0" ∧
    currentBoundedProgramId = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0" ∧
    currentBoundedProgramState = "CLOSED" ∧
    currentBoundedAttemptNumber = 1 ∧ selectedSourceCount = 96 ∧
    contentPassesConsumed = 1 ∧ contractRecoveryPerformed = false ∧
    stageTwoAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
