import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.ToeCCFTV0ViabilityHandoffStage5OpenAuthorityReviewV0
import ToeFormal.Release.ToeCCFTV0ViabilityHandoffStage5OpenAuthorityV0

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

theorem current_authority_tracks_terminal_closeout_without_successor_authority :
    boundedProgramState = "CLOSED_AFTER_MANDATORY_EXIT" ∧ boundedAttemptNumber = 5 ∧
    Derivation.ToeCCFTV0TheoryConstructionAndTheoremDiscoveryV0BoundedCloseout.frozenModelPreserved = true ∧
    Derivation.ToeCCFTV0TheoryConstructionAndTheoremDiscoveryV0BoundedCloseout.mathematicalNoveltyEstablished = false ∧
    Derivation.ToeCCFTV0TheoryConstructionAndTheoremDiscoveryV0BoundedCloseout.physicalInterpretationEstablished = false ∧
    Derivation.ToeCCFTV0TheoryConstructionAndTheoremDiscoveryV0BoundedCloseout.scientificSuccessorAuthorized = false := by
  native_decide

theorem stage_five_authority_and_review_remain_bound :
    ToeCCFTV0ViabilityHandoffStage5OpenAuthorityV0.stageFiveOpenAuthorized = true ∧
    ToeCCFTV0ViabilityHandoffStage5OpenAuthorityReviewV0.reviewAccepted = true := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
