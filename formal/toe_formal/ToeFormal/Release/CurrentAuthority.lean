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

theorem current_authority_tracks_closed_stage_four_without_stage_five_authority :
    ToeCCFTV0PrimaryTheoremAttackStage4OpenAuthorityReviewV0.reviewAccepted = true ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackResult.linkedClaimCount = 4 ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackResult.theoremGradeClaimsEstablished = 3 ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackResult.historicalRecordsClassified = 2 ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackResult.frozenModelMutated = false ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackResult.frozenPacketMutated = false ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackResult.physicalPromotionPerformed = false ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackResult.stageFiveAuthorized = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
