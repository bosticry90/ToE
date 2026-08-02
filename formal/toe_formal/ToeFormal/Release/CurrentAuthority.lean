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

theorem current_authority_tracks_frozen_packet_without_stage_four_authority :
    ToeCCFTV0PrimaryTheoremPacketStage3OpenAuthorityReviewV0.reviewAccepted = true ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketResult.attemptSequenceNumber = 3 ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketResult.primaryPacketCount = 1 ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketResult.linkedClaimCount = 4 ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketResult.formalPropositionCount = 4 ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketResult.formalNegationCount = 4 ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketResult.packetFrozen = true ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketResult.proofExecuted = false ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketResult.counterexampleFound = false ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketResult.mathematicalViabilityEstablished = false ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketResult.physicalInterpretationEstablished = false ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketResult.stageFourAuthorized = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
