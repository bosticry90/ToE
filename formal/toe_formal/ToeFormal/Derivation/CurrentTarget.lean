import ToeFormal.Derivation.ToeTargetedCCFTContractAdjudicationAttemptOpen

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeTargetedCCFTContractAdjudicationAttemptOpen

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := scientificTarget
def currentEvidencePacketId : String := eventId
def currentBoundedProgramId : String := programId
def currentBoundedProgramState : String := "OPEN"
def currentTargetPhase : String := "TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION_STAGE_3_OPEN"
def currentBoundedAttemptNumber : Nat := attemptNumber
def lastClosedBoundedSemanticStage : String := "TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION"
def lastBoundedTerminalResult : String := "TARGETED_CCFT_CONTRACT_EXTRACTION_COMPLETE"

theorem current_target_opens_adjudication_without_result :
    currentLiveTarget = "adjudicate_toe_targeted_ccft_contract_completeness_and_conflicts_v0" ∧ currentBoundedProgramId = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0" ∧
    currentBoundedProgramState = "OPEN" ∧ currentBoundedAttemptNumber = 3 ∧
    contractRecordCount = 23 ∧ exactCandidateCount = 7 ∧
    adjudicationRecordsCreated = 0 ∧ contractRecoveredOrRejected = false ∧
    theoremDiscoveryOpened = false ∧ stageFourAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
