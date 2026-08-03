import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.ToeCCFTV0PrimaryTheoremAttackStage4OpenAuthorityReviewV0

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def currentBoundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState

theorem current_authority_tracks_empty_bounded_stage_four_open :
    ToeCCFTV0PrimaryTheoremAttackStage4OpenAuthorityReviewV0.reviewAccepted = true ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackAttemptOpen.attemptNumber = 4 ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackAttemptOpen.frozenPacketCount = 1 ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackAttemptOpen.linkedClaimCount = 4 ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackAttemptOpen.theoremResultCount = 0 ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackAttemptOpen.modelMutated = false ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackAttemptOpen.packetMutated = false ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackAttemptOpen.physicalPromotion = false ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackAttemptOpen.stageFiveAuthorized = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
