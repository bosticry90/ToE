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

theorem current_authority_tracks_open_ccft_object_operationalization :
    currentTarget = "operationalize_toe_retained_ccft_mathematical_objects_v0" := by
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

theorem ccft_object_operationalization_stage_three_is_open_without_scientific_result :
    boundedProgramId =
      "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_V0" ∧
    boundedProgramState = "OPEN" ∧
    currentTargetPhase = "STAGE_3_OPEN_NO_SCIENTIFIC_RESULT" ∧
    boundedAttemptNumber = 3 ∧
    Derivation.ToeCCFTMathematicalObjectOperationalizationAttemptOpen.operationalRecordsCreatedAtOpen = 0 ∧
    Derivation.ToeCCFTMathematicalObjectOperationalizationAttemptOpen.objectsOperationallyDefinedAtOpen = 0 ∧
    Derivation.ToeCCFTMathematicalObjectOperationalizationAttemptOpen.boundedSurrogateInterpretationsAdoptedAtOpen = 0 ∧
    Derivation.ToeCCFTMathematicalObjectOperationalizationAttemptOpen.preferredFormulationOrMinimalCoreSelected = false ∧
    Derivation.ToeCCFTMathematicalObjectOperationalizationAttemptOpen.representationFieldActionSeamOrObservableSelected = false ∧
    Derivation.ToeCCFTMathematicalObjectOperationalizationAttemptOpen.evidencePromoted = false ∧
    Derivation.ToeCCFTMathematicalObjectOperationalizationAttemptOpen.stageFourAuthorized = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
