import ToeFormal.Derivation.ToeTargetedCCFTRecoveryHandoffAttemptOpen

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeTargetedCCFTRecoveryHandoffAttemptOpen

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := scientificTarget
def currentEvidencePacketId : String := eventId
def currentBoundedProgramId : String := programId
def currentBoundedProgramState : String := "OPEN"
def currentTargetPhase : String := "TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_STAGE_4_OPEN"
def currentBoundedAttemptNumber : Nat := attemptNumber
def lastClosedBoundedSemanticStage : String := "TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION"
def lastBoundedTerminalResult : String := "ONE_OR_MORE_EXACT_CCFT_CLOSURE_CONTRACTS_RECOVERED"

theorem current_target_opens_handoff_without_result :
    currentLiveTarget = "select_toe_post_targeted_ccft_recovery_construction_handoff_v0" ∧ currentBoundedProgramId = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0" ∧
    currentBoundedProgramState = "OPEN" ∧ currentBoundedAttemptNumber = 4 ∧
    exactContractsRecovered = 4 ∧ programOutcomeSelected = false ∧
    branchSelected = false ∧ ccftV0Constructed = false ∧
    constructionPreparationAuthorized = false ∧ theoremDiscoveryAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
