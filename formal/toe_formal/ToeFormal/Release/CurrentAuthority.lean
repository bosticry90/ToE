import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.ToeTargetedCCFTRecoveryHandoffStage4OpenAuthorityReviewV0
import ToeFormal.Release.ToeTargetedCCFTRecoveryHandoffStage4OpenAuthorityV0

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def boundedProgramId : String := Derivation.CurrentTarget.currentBoundedProgramId
def boundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def boundedAttemptNumber : Nat := Derivation.CurrentTarget.currentBoundedAttemptNumber

theorem current_authority_tracks_terminal_closeout_without_construction_authority :
    currentTarget = "close_toe_targeted_ccft_closure_evidence_recovery_v0_after_bounded_result_v0" ∧
    boundedProgramState = "CLOSED_AFTER_MANDATORY_EXIT" ∧ boundedAttemptNumber = 4 ∧
    Derivation.ToeTargetedCCFTClosureEvidenceRecoveryV0BoundedCloseout.recoveredContractCount = 4 ∧
    Derivation.ToeTargetedCCFTClosureEvidenceRecoveryV0BoundedCloseout.constructionPreparationAuthorized = false ∧
    Derivation.ToeTargetedCCFTClosureEvidenceRecoveryV0BoundedCloseout.theoremDiscoveryAuthorized = false := by
  native_decide

theorem stage_four_authority_and_review_remain_bound :
    ToeTargetedCCFTRecoveryHandoffStage4OpenAuthorityV0.stageFourOpenAuthorized = true ∧
    ToeTargetedCCFTRecoveryHandoffStage4OpenAuthorityReviewV0.accepted = true := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
