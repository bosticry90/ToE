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

theorem current_authority_tracks_open_minimal_ccft_surrogate_core_decision :
    currentTarget = "select_or_reject_toe_minimal_closed_ccft_core_v0" := by
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

theorem minimal_ccft_surrogate_core_stage_four_is_open_without_result :
    boundedProgramId =
      "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_V0" ∧
    boundedProgramState = "OPEN" ∧
    currentTargetPhase = "STAGE_4_OPEN_NO_SCIENTIFIC_RESULT" ∧
    boundedAttemptNumber = 4 ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionAttemptOpen.operationalRecordCount = 20 ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionAttemptOpen.boundedSurrogateRecordCount = 5 ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionAttemptOpen.fullyPhysicallyOperationalObjectCount = 0 ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionAttemptOpen.candidateCoreRowsEvaluatedAtOpen = 0 ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionAttemptOpen.closureMatrixCellsPopulatedAtOpen = 0 ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionAttemptOpen.minimalCoreSelected = false ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionAttemptOpen.newPostulateInserted = false ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionAttemptOpen.physicalCCFTModelEstablished = false ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionAttemptOpen.actionSeamObservableOrViabilityTestCreated = false ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionAttemptOpen.evidencePromoted = false ∧
    Derivation.ToeMinimalClosedCCFTCoreDecisionAttemptOpen.stageFiveAuthorized = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
