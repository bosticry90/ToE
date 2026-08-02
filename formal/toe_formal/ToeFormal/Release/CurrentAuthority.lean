import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.ToeTargetedCCFTClosureContractExtractionStage2OpenAuthorityV0
import ToeFormal.Release.ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityV0
import ToeFormal.Release.ToeTargetedCCFTContractAdjudicationStage3OpenAuthorityV0
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

theorem current_authority_tracks_open_stage_four_without_result :
    currentTarget = "select_toe_post_targeted_ccft_recovery_construction_handoff_v0" ∧ boundedProgramId = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0" ∧
    boundedProgramState = "OPEN" ∧ boundedAttemptNumber = 4 ∧
    Derivation.ToeTargetedCCFTRecoveryHandoffAttemptOpen.programOutcomeSelected = false ∧
    Derivation.ToeTargetedCCFTRecoveryHandoffAttemptOpen.constructionPreparationAuthorized = false ∧
    Derivation.ToeTargetedCCFTRecoveryHandoffAttemptOpen.theoremDiscoveryAuthorized = false := by
  native_decide

theorem all_four_stage_authorities_remain_bound :
    ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityV0.stageOneOpenAuthorized = true ∧
    ToeTargetedCCFTClosureContractExtractionStage2OpenAuthorityV0.stageTwoOpenAuthorized = true ∧
    ToeTargetedCCFTContractAdjudicationStage3OpenAuthorityV0.stageThreeOpenAuthorized = true ∧
    ToeTargetedCCFTRecoveryHandoffStage4OpenAuthorityV0.stageFourOpenAuthorized = true ∧
    ToeTargetedCCFTRecoveryHandoffStage4OpenAuthorityReviewV0.accepted = true := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
