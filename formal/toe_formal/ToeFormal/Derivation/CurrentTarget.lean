import ToeFormal.Derivation.ToeCCFTV0ViabilityHandoffResult

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeCCFTV0ViabilityHandoffResult
def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := mandatoryExitTarget
def currentEvidencePacketId : String := resultId
def currentTargetPhase : String :=
  "CCFT_V0_INTERNAL_VIABILITY_AND_DISTINCTIVENESS_HANDOFF_STAGE_5_CLOSED_PASSED"
def currentBoundedProgramState : String := "CLOSED_AWAITING_MANDATORY_EXIT"

theorem current_target_is_mandatory_exit_after_bounded_stage_five_result :
    attemptSequenceNumber = 5 ∧ frozenModelCount = 1 ∧ assessmentSurfaceCount = 6 ∧
    knownModelEquivalent = true ∧ mathematicallyDistinctive = false ∧
    reproducibleInFrozenTestRegime = true ∧
    fullPDEViabilityIndependentlyAdjudicated = false ∧
    identifiableAsDistinctIsolatedDynamics = false ∧
    frozenReferenceComputationsTractable = true ∧ modelPreserved = true ∧
    mandatoryExitSelected = true ∧ mandatoryExitCompleted = false ∧
    scientificSuccessorAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
