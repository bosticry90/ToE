import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.ToeCCFTV0BranchReadinessStage1OpenAuthorityReviewV0

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def currentBoundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState

theorem current_authority_tracks_valid_nonselecting_open :
    ToeCCFTV0BranchReadinessStage1OpenAuthorityReviewV0.reviewAccepted = true ∧
    Derivation.ToeCCFTV0BranchReadinessAttemptOpen.attemptNumber = 1 ∧
    Derivation.ToeCCFTV0BranchReadinessAttemptOpen.branchSelected = false ∧
    Derivation.ToeCCFTV0BranchReadinessAttemptOpen.modelConstructed = false ∧
    Derivation.ToeCCFTV0BranchReadinessAttemptOpen.stageTwoAuthorized = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
