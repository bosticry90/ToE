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

theorem current_authority_tracks_closed_stage_five_and_mandatory_exit :
    ToeCCFTV0ViabilityHandoffStage5OpenAuthorityReviewV0.reviewAccepted = true ∧
    Derivation.ToeCCFTV0ViabilityHandoffResult.attemptSequenceNumber = 5 ∧
    Derivation.ToeCCFTV0ViabilityHandoffResult.knownModelEquivalent = true ∧
    Derivation.ToeCCFTV0ViabilityHandoffResult.mathematicallyDistinctive = false ∧
    Derivation.ToeCCFTV0ViabilityHandoffResult.modelPreserved = true ∧
    Derivation.ToeCCFTV0ViabilityHandoffResult.mandatoryExitSelected = true ∧
    Derivation.ToeCCFTV0ViabilityHandoffResult.mandatoryExitCompleted = false ∧
    Derivation.ToeCCFTV0ViabilityHandoffResult.physicalBearerAssigned = false ∧
    Derivation.ToeCCFTV0ViabilityHandoffResult.empiricalClaimCreated = false ∧
    Derivation.ToeCCFTV0ViabilityHandoffResult.scientificSuccessorAuthorized = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
