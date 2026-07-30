import ToeFormal.Derivation.ToeNativeCoherenceOntologyAndRepresentationV0BoundedCloseout

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
  "close_toe_native_coherence_ontology_and_representation_v0_after_bounded_result_v0"

def currentEvidencePacketId : String :=
  ToeNativeCoherenceOntologyAndRepresentationV0BoundedCloseout.calculationId

def currentBoundedProgramId : String :=
  "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0"

def currentBoundedProgramState : String := "TERMINAL"

def currentTargetPhase : String :=
  "PROGRAM_CLOSED_AFTER_MANDATORY_EXIT"

def currentBoundedAttemptNumber : Nat := 2

def lastClosedBoundedSemanticStage : String :=
  "COHERENCE_OPERATIONAL_DEFINITION_TEST"

def lastBoundedTerminalResult : String := "BLOCKED"

theorem current_target_records_completed_mandatory_bounded_exit :
    currentLiveTarget =
      "close_toe_native_coherence_ontology_and_representation_v0_after_bounded_result_v0" := by
  rfl

theorem coherence_program_is_terminal_after_operational_definition_block :
    currentBoundedProgramId =
      "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0" ∧
    currentBoundedProgramState = "TERMINAL" ∧
    currentTargetPhase =
      "PROGRAM_CLOSED_AFTER_MANDATORY_EXIT" ∧
    currentBoundedAttemptNumber = 2 ∧
    lastClosedBoundedSemanticStage =
      "COHERENCE_OPERATIONAL_DEFINITION_TEST" ∧
    lastBoundedTerminalResult = "BLOCKED" ∧
    ToeNativeCoherenceOntologyAndRepresentationV0BoundedCloseout.automaticSuccessorSelected =
      false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
