import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationV0
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationResultReviewV0
import ToeFormal.Release.ToeTargetedCCFTClosureContractExtractionStage2OpenAuthorityReviewV0
import ToeFormal.Release.ToeTargetedCCFTClosureContractExtractionStage2OpenAuthorityV0
import ToeFormal.Release.ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityReviewV0
import ToeFormal.Release.ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityV0

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

theorem current_authority_tracks_open_contract_extraction_without_output :
    currentTarget = "extract_toe_targeted_ccft_closure_contracts_v0" ∧
    boundedProgramId = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0" ∧
    boundedProgramState = "OPEN" ∧ boundedAttemptNumber = 2 ∧
    Derivation.ToeTargetedCCFTClosureContractExtractionAttemptOpen.selectedSourceCount = 96 ∧
    Derivation.ToeTargetedCCFTClosureContractExtractionAttemptOpen.contractRecordsExtracted = 0 ∧
    Derivation.ToeTargetedCCFTClosureContractExtractionAttemptOpen.contractRecoveredOrRejected =
      false ∧
    Derivation.ToeTargetedCCFTClosureContractExtractionAttemptOpen.stageThreeAuthorized = false := by
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

theorem stage_one_authority_and_review_remain_bound :
    ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityV0.stageOneOpenAuthorized =
      true ∧
    ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityReviewV0.accepted =
      true := by
  native_decide

theorem stage_two_authority_and_review_are_current :
    ToeTargetedCCFTClosureContractExtractionStage2OpenAuthorityV0.stageTwoOpenAuthorized =
      true ∧
    ToeTargetedCCFTClosureContractExtractionStage2OpenAuthorityReviewV0.accepted = true ∧
    ToeTargetedCCFTClosureContractExtractionStage2OpenAuthorityV0.stageThreeAuthorized =
      false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
