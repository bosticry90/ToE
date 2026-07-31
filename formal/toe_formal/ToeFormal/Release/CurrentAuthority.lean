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

theorem current_authority_tracks_open_ccft_lineage_reconciliation :
    currentTarget =
      "reconstruct_toe_ccft_mathematical_lineages_and_conflicts_v0" := by
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

theorem ccft_lineage_stage_two_is_open_without_scientific_result :
    boundedProgramId =
      "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_V0" ∧
    boundedProgramState = "OPEN" ∧
    currentTargetPhase = "STAGE_2_OPEN_NO_SCIENTIFIC_RESULT" ∧
    boundedAttemptNumber = 2 ∧
    Derivation.ToeCCFTMathematicalLineageAndConflictReconciliationAttemptOpen.lineageRelationshipsEstablishedAtOpen =
      0 ∧
    Derivation.ToeCCFTMathematicalLineageAndConflictReconciliationAttemptOpen.preferredFormulationOrMinimalCoreSelected =
      false ∧
    Derivation.ToeCCFTMathematicalLineageAndConflictReconciliationAttemptOpen.physicalInterpretationEstablished =
      false ∧
    Derivation.ToeCCFTMathematicalLineageAndConflictReconciliationAttemptOpen.stageThreeAuthorized =
      false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
