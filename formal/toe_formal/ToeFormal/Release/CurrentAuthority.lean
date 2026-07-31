import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationResultReviewV0
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationV0
import ToeFormal.Release.ToeCCFTCoreProgramGovernanceInstallationV0

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String :=
  Derivation.CurrentTarget.currentEvidencePacketId
def boundedProgramId : String := Derivation.CurrentTarget.currentBoundedProgramId
def boundedProgramState : String :=
  Derivation.CurrentTarget.currentBoundedProgramState
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def boundedAttemptNumber : Nat :=
  Derivation.CurrentTarget.currentBoundedAttemptNumber

theorem current_authority_tracks_installed_ccft_core_program :
    currentTarget =
      "prepare_toe_ccft_native_mathematical_core_and_operationalization_bounded_program_v0" := by
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

theorem ccft_core_program_is_installed_and_remains_unopened :
    boundedProgramId =
      "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_V0" ∧
    boundedProgramState = "UNOPENED" ∧
    currentTargetPhase =
      "PROGRAM_INSTALLED_AWAITING_SEPARATE_STAGE_1_AUTHORITY" ∧
    boundedAttemptNumber = 0 ∧
    ToeCCFTCoreProgramGovernanceInstallationV0.programInstalled = true ∧
    ToeCCFTCoreProgramGovernanceInstallationV0.programOpened = false ∧
    ToeCCFTCoreProgramGovernanceInstallationV0.scientificOutputCreated = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
