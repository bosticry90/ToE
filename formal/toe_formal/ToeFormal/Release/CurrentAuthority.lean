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

theorem current_authority_tracks_open_requirement_family_compatibility_survey :
    currentTarget =
      "survey_toe_source_bound_gravitational_requirement_family_compatibility_v0" := by
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

theorem requirement_family_compatibility_survey_stage_is_open_without_result :
    boundedProgramId =
      "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0" ∧
    boundedProgramState = "OPEN" ∧
    currentTargetPhase =
      "STAGE_4_SCIENTIFIC_ATTEMPT_OPEN" ∧
    boundedAttemptNumber = 4 ∧
    Derivation.ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyAttemptOpen.programOpen =
      true ∧
    Derivation.ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyAttemptOpen.scientificResultCreated =
      false ∧
    Derivation.ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyAttemptOpen.compatibilityCellsPopulated =
      0 ∧
    Derivation.ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyAttemptOpen.familiesEligibleForNativeSelection =
      0 ∧
    Derivation.ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyAttemptOpen.evidencePromoted =
      false ∧
    Derivation.ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyAttemptOpen.gravitationalActionSelected =
      false ∧
    Derivation.ToeSourceBoundGravitationalRequirementFamilyCompatibilitySurveyAttemptOpen.stageFiveAuthorized =
      false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
