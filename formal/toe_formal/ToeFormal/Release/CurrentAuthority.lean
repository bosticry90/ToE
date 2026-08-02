import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.ToeCCFTV0ModelContractFreezeStage2OpenAuthorityReviewV0

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def currentBoundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState

theorem current_authority_tracks_empty_bounded_stage_two_open :
    ToeCCFTV0ModelContractFreezeStage2OpenAuthorityReviewV0.reviewAccepted = true ∧
    Derivation.ToeCCFTV0ModelContractFreezeAttemptOpen.selectedBranch = "CP_NLSE" ∧
    Derivation.ToeCCFTV0ModelContractFreezeAttemptOpen.governingEquationSelected = false ∧
    Derivation.ToeCCFTV0ModelContractFreezeAttemptOpen.newPostulateCount = 0 ∧
    Derivation.ToeCCFTV0ModelContractFreezeAttemptOpen.modelConstructed = false ∧
    Derivation.ToeCCFTV0ModelContractFreezeAttemptOpen.theoremAttempted = false ∧
    Derivation.ToeCCFTV0ModelContractFreezeAttemptOpen.stageThreeAuthorized = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
