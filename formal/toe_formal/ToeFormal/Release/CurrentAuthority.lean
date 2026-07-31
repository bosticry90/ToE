import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationV0
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationResultReviewV0

/-
Release-facing current-authority aggregate for tiered validation. It is a small
build target for authority-surface synchronization checks and intentionally
does not replace the full ToeFormal release aggregate.
-/

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"

def currentTarget : String :=
  Derivation.CurrentTarget.currentLiveTarget

def currentEvidencePacketId : String :=
  Derivation.CurrentTarget.currentEvidencePacketId

def boundedProgramId : String :=
  Derivation.CurrentTarget.currentBoundedProgramId

def boundedProgramState : String :=
  Derivation.CurrentTarget.currentBoundedProgramState

def currentTargetPhase : String :=
  Derivation.CurrentTarget.currentTargetPhase

def boundedAttemptNumber : Nat :=
  Derivation.CurrentTarget.currentBoundedAttemptNumber

theorem current_authority_tracks_open_candidate_action_family_inventory :
    currentTarget =
      "inventory_toe_candidate_gravitational_action_families_v0" := by
  native_decide

theorem bounded_program_governance_installation_preserved_its_then_current_target :
    BoundedProgramGovernanceControlInstallationV0.scientificTarget =
      "prepare_qft_gr_quadratic_generic_background_linearization_gauge_and_jet_contract_v0" ∧
    BoundedProgramGovernanceControlInstallationV0.scientificTargetRotated =
      false := by
  native_decide

theorem bounded_program_governance_review_preserved_its_then_current_target :
    BoundedProgramGovernanceControlInstallationResultReviewV0.scientificTarget =
      "prepare_qft_gr_quadratic_generic_background_linearization_gauge_and_jet_contract_v0" := by
  native_decide

theorem candidate_action_family_inventory_stage_is_open_without_result :
    boundedProgramId =
      "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0" ∧
    boundedProgramState = "OPEN" ∧
    currentTargetPhase =
      "STAGE_2_SCIENTIFIC_ATTEMPT_OPEN" ∧
    boundedAttemptNumber = 2 ∧
    Derivation.ToeCandidateGravitationalActionFamilyInventoryAttemptOpen.programOpen =
      true ∧
    Derivation.ToeCandidateGravitationalActionFamilyInventoryAttemptOpen.scientificResultCreated =
      false ∧
    Derivation.ToeCandidateGravitationalActionFamilyInventoryAttemptOpen.actionFamiliesCompared =
      false ∧
    Derivation.ToeCandidateGravitationalActionFamilyInventoryAttemptOpen.gravitationalActionSelected =
      false ∧
    Derivation.ToeCandidateGravitationalActionFamilyInventoryAttemptOpen.stageThreeAuthorized =
      false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
