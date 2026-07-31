import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationResultReviewV0
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationV0
import ToeFormal.Release.ToePositiveGravitationalPrincipleProgramGovernanceInstallationResultReviewV0
import ToeFormal.Release.ToePositiveGravitationalPrincipleProgramGovernanceInstallationV0

namespace ToeFormal
namespace Release
namespace CurrentAuthority

open Derivation.ToePositiveGravitationalPrincipleSourceInventoryAttemptOpen

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

theorem current_authority_tracks_open_positive_principle_source_inventory :
    currentTarget =
      "inventory_toe_positive_native_gravitational_principle_sources_v0" := by
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

theorem positive_principle_source_inventory_attempt_is_open_without_result :
    boundedProgramId =
      "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_V0" ∧
    boundedProgramState = "OPEN" ∧
    currentTargetPhase = "STAGE_1_SCIENTIFIC_ATTEMPT_OPEN" ∧
    boundedAttemptNumber = 1 ∧
    ToePositiveGravitationalPrincipleProgramGovernanceInstallationV0.programInstalled =
      true ∧
    ToePositiveGravitationalPrincipleProgramGovernanceInstallationV0.programOpened =
      false ∧
    ToePositiveGravitationalPrincipleProgramGovernanceInstallationResultReviewV0.installationAccepted =
      true ∧
    programOpen = true ∧ scientificResultCreated = false ∧
    principleSourceStatementsInventoried = 0 ∧
    principleSelectedOrDerived = false ∧
    gravitationalVariablesSelected = false ∧ actionClassSelected = false ∧
    gravitationalActionConstructedOrSelected = false ∧
    gravitationalCalculationStarted = false ∧ evidencePromoted = false ∧
    stageTwoAuthorized = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
