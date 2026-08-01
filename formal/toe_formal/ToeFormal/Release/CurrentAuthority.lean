import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationV0
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationResultReviewV0
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

theorem current_authority_tracks_open_targeted_source_discovery_stage :
    currentTarget =
      "discover_toe_targeted_ccft_closure_evidence_sources_v0" := by
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

theorem targeted_source_discovery_stage_is_open_without_scientific_output :
    boundedProgramId = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0" ∧
    boundedProgramState = "OPEN" ∧
    currentTargetPhase =
      "TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_STAGE_1_OPEN" ∧
    boundedAttemptNumber = 1 ∧
    ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityV0.stageOneOpenAuthorized =
      true ∧
    ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityReviewV0.accepted =
      true ∧
    Derivation.ToeTargetedCCFTClosureSourceDiscoveryAttemptOpen.programOpen = true ∧
    Derivation.ToeTargetedCCFTClosureSourceDiscoveryAttemptOpen.scientificResultCreated =
      false ∧
    Derivation.ToeTargetedCCFTClosureSourceDiscoveryAttemptOpen.rootsTraversed = 0 ∧
    Derivation.ToeTargetedCCFTClosureSourceDiscoveryAttemptOpen.contentPassesConsumed =
      0 ∧
    Derivation.ToeTargetedCCFTClosureSourceDiscoveryAttemptOpen.stageTwoAuthorized =
      false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
