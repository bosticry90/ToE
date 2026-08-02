import ToeFormal.Derivation.ToeTargetedCCFTContractAdjudicationResult

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeTargetedCCFTContractAdjudicationResult

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := selectedNextTarget
def currentEvidencePacketId : String := resultId
def currentBoundedProgramId : String := programId
def currentBoundedProgramState : String := "CLOSED"
def currentTargetPhase : String := "TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION_STAGE_3_CLOSED_PASSED"
def currentBoundedAttemptNumber : Nat := attemptSequenceNumber
def lastClosedBoundedSemanticStage : String := semanticStageId
def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_selects_stage_four_without_authorizing_it :
    currentLiveTarget = "select_toe_post_targeted_ccft_recovery_construction_handoff_v0" ∧ currentBoundedProgramId = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0" ∧
    currentBoundedProgramState = "CLOSED" ∧ currentBoundedAttemptNumber = 3 ∧
    exactContractsRecovered = 4 ∧ conflictsPreserved = 3 ∧
    theoremDiscoveryOpened = false ∧ stageFourAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
