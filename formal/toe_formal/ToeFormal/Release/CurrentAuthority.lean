import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.ToeCCFTV0PrimaryTheoremPacketStage3OpenAuthorityReviewV0

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def currentBoundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState

theorem current_authority_tracks_empty_bounded_stage_three_open :
    ToeCCFTV0PrimaryTheoremPacketStage3OpenAuthorityReviewV0.reviewAccepted = true ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketAttemptOpen.attemptNumber = 3 ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketAttemptOpen.frozenPacketCount = 0 ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketAttemptOpen.frozenPropositionCount = 0 ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketAttemptOpen.theoremResultCount = 0 ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketAttemptOpen.modelMutated = false ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketAttemptOpen.physicalPromotion = false ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketAttemptOpen.stageFourAuthorized = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
