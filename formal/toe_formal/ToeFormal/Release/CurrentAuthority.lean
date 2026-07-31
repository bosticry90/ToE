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

theorem current_authority_tracks_selected_unopened_eligibility_handoff :
    currentTarget =
      "select_toe_gravitational_action_family_eligibility_handoff_v0" := by
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

theorem compatibility_survey_is_closed_without_action_selection_or_stage_five_authority :
    boundedProgramId =
      "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0" ∧
    boundedProgramState = "CLOSED" ∧
    currentTargetPhase =
      "STAGE_5_SELECTED_UNOPENED_AFTER_STAGE_4_PASS" ∧
    boundedAttemptNumber = 4 ∧
    Derivation.ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyResult.compatibilityCellCount =
      70 ∧
    Derivation.ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyResult.observedDefinedNativeActionFamilyCount =
      0 ∧
    Derivation.ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyResult.gravitationalActionsSelected =
      0 ∧
    Derivation.ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyResult.nativeGravitationalPrinciplesDerivedOrPostulated =
      0 ∧
    Derivation.ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyResult.newGravitationalCalculationsExecuted =
      0 ∧
    Derivation.ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyResult.stageFiveEligibilityVerdictMade =
      false ∧
    Derivation.ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyResult.stageFiveAuthorized =
      false ∧
    Derivation.ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyResult.stageFiveOpened =
      false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
