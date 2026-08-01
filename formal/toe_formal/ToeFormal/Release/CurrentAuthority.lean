import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationV0
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationResultReviewV0

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

theorem current_authority_tracks_mandatory_ccft_core_program_exit :
    currentTarget =
      "close_toe_ccft_native_mathematical_core_and_operationalization_v0_after_bounded_result_v0" := by
  native_decide

theorem bounded_program_governance_installation_preserved_its_then_current_target :
    BoundedProgramGovernanceControlInstallationV0.scientificTarget =
      "prepare_qft_gr_quadratic_generic_background_linearization_gauge_and_jet_contract_v0" ∧
    BoundedProgramGovernanceControlInstallationV0.scientificTargetRotated = false := by
  native_decide

theorem bounded_program_governance_review_preserved_its_then_current_target :
    BoundedProgramGovernanceControlInstallationResultReviewV0.scientificTarget =
      "prepare_qft_gr_quadratic_generic_background_linearization_gauge_and_jet_contract_v0" := by
  native_decide

theorem minimal_ccft_surrogate_core_stage_four_is_closed_and_blocked :
    boundedProgramId =
      "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_V0" ∧
    boundedProgramState = "CLOSED" ∧
    currentTargetPhase = "STAGE_4_CLOSED_BLOCKED_AWAITING_MANDATORY_EXIT" ∧
    boundedAttemptNumber = 4 ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionResult.candidateCount = 2 ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionResult.closureCellCount = 24 ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionResult.minimalCoreSelected = false ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionResult.cpNlseCoreSelected = false ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionResult.lcrdV3CoreSelected = false ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionResult.newPostulateInserted = false ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionResult.physicalCCFTModelEstablished = false ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionResult.actionSeamObservableOrViabilityTestCreated = false ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionResult.evidencePromoted = false ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionResult.stageBlocked = true ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionResult.mandatoryExitCompleted = false ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionResult.stageFiveAuthorized = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
