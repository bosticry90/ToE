import ToeFormal.Derivation.ToeGravitationalRequirementAndActionFamilyLineageReconstructionAttemptOpen

/-
Thin current-target aggregate for tiered validation. This target follows the
live strict target and avoids requiring a full ToeFormal aggregate build for
routine packet checks.
-/

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  ToeGravitationalRequirementAndActionFamilyLineageReconstructionAttemptOpen.scientificTarget

def currentEvidencePacketId : String :=
  ToeGravitationalRequirementAndActionFamilyLineageReconstructionAttemptOpen.eventId

def currentBoundedProgramId : String :=
  ToeGravitationalRequirementAndActionFamilyLineageReconstructionAttemptOpen.programId

def currentBoundedProgramState : String := "OPEN"

def currentTargetPhase : String :=
  "STAGE_3_SCIENTIFIC_ATTEMPT_OPEN"

def currentBoundedAttemptNumber : Nat :=
  ToeGravitationalRequirementAndActionFamilyLineageReconstructionAttemptOpen.attemptSequenceNumber

def lastClosedBoundedSemanticStage : String :=
  "CANDIDATE_GRAVITATIONAL_ACTION_FAMILY_INVENTORY"

def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_records_open_gravitational_lineage_reconstruction :
    currentLiveTarget =
      "reconstruct_toe_gravitational_requirement_and_action_family_lineages_v0" := by
  rfl

theorem gravitational_lineage_reconstruction_is_open_without_result :
    currentBoundedProgramId =
      "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0" ∧
    currentBoundedProgramState = "OPEN" ∧
    currentTargetPhase =
      "STAGE_3_SCIENTIFIC_ATTEMPT_OPEN" ∧
    currentBoundedAttemptNumber = 3 ∧
    lastClosedBoundedSemanticStage =
      "CANDIDATE_GRAVITATIONAL_ACTION_FAMILY_INVENTORY" ∧
    lastBoundedTerminalResult = "PASSED" ∧
    ToeGravitationalRequirementAndActionFamilyLineageReconstructionAttemptOpen.programOpen = true ∧
    ToeGravitationalRequirementAndActionFamilyLineageReconstructionAttemptOpen.scientificResultCreated = false ∧
    ToeGravitationalRequirementAndActionFamilyLineageReconstructionAttemptOpen.documentaryRelationshipsReconstructed = 0 ∧
    ToeGravitationalRequirementAndActionFamilyLineageReconstructionAttemptOpen.actionDefinitionsRecovered = 0 ∧
    ToeGravitationalRequirementAndActionFamilyLineageReconstructionAttemptOpen.compatibilityJudgmentsMade = false ∧
    ToeGravitationalRequirementAndActionFamilyLineageReconstructionAttemptOpen.gravitationalActionSelected = false ∧
    ToeGravitationalRequirementAndActionFamilyLineageReconstructionAttemptOpen.stageFourAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
