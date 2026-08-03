import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.ToeCCFTV0ViabilityHandoffStage5OpenAuthorityReviewV0

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def currentBoundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState

theorem current_authority_tracks_empty_bounded_stage_five_open :
    ToeCCFTV0ViabilityHandoffStage5OpenAuthorityReviewV0.reviewAccepted = true ∧
    Derivation.ToeCCFTV0ViabilityHandoffAttemptOpen.attemptNumber = 5 ∧
    Derivation.ToeCCFTV0ViabilityHandoffAttemptOpen.frozenModelCount = 1 ∧
    Derivation.ToeCCFTV0ViabilityHandoffAttemptOpen.assessmentSurfaceCount = 6 ∧
    Derivation.ToeCCFTV0ViabilityHandoffAttemptOpen.assessmentResultCount = 0 ∧
    Derivation.ToeCCFTV0ViabilityHandoffAttemptOpen.selectedFutureRoleCount = 0 ∧
    Derivation.ToeCCFTV0ViabilityHandoffAttemptOpen.modelMutated = false ∧
    Derivation.ToeCCFTV0ViabilityHandoffAttemptOpen.CCFTV1Constructed = false ∧
    Derivation.ToeCCFTV0ViabilityHandoffAttemptOpen.physicalPromotion = false ∧
    Derivation.ToeCCFTV0ViabilityHandoffAttemptOpen.successorAuthorized = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
