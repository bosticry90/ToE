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

theorem current_authority_tracks_selected_unopened_minimal_ccft_core_decision :
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

theorem ccft_object_operationalization_stage_three_is_closed_surrogate_only :
    boundedProgramId =
      "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_V0" ∧
    boundedProgramState = "CLOSED" ∧
    currentTargetPhase =
      "STAGE_3_CLOSED_PASSED_BOUNDED_SURROGATES_AWAITING_SEPARATE_STAGE_4_AUTHORITY" ∧
    boundedAttemptNumber = 3 ∧
    Derivation.ToeCCFTMathematicalObjectOperationalizationResult.operationalizationCompleted = true ∧
    Derivation.ToeCCFTMathematicalObjectOperationalizationResult.fullyPhysicallyOperationalObjectCount = 0 ∧
    Derivation.ToeCCFTMathematicalObjectOperationalizationResult.boundedSurrogateRecordCount = 5 ∧
    Derivation.ToeCCFTMathematicalObjectOperationalizationResult.distinctivePhysicalCCFTQuantityEstablished = false ∧
    Derivation.ToeCCFTMathematicalObjectOperationalizationResult.preferredFormulationSelected = false ∧
    Derivation.ToeCCFTMathematicalObjectOperationalizationResult.minimalCoreSelected = false ∧
    Derivation.ToeCCFTMathematicalObjectOperationalizationResult.ccftActionConstructed = false ∧
    Derivation.ToeCCFTMathematicalObjectOperationalizationResult.seamOrObservableDefined = false ∧
    Derivation.ToeCCFTMathematicalObjectOperationalizationResult.stageFourAuthorized = false ∧
    Derivation.ToeCCFTMathematicalObjectOperationalizationResult.stageFourOpened = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
