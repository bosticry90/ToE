import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Derivation.ToeCCFTV0TheoryConstructionBoundedProgramPreparationAuthority

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def currentBoundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState

theorem current_authority_tracks_prepared_uninstalled_ccft_v0_program :
    currentTarget = "prepare_bounded_ccft_v0_theory_construction_program" ∧
    Derivation.ToeCCFTV0TheoryConstructionBoundedProgramPreparationResultReview.programInstalled = false ∧
    Derivation.ToeCCFTV0TheoryConstructionBoundedProgramPreparationResultReview.branchSelected = false ∧
    Derivation.ToeCCFTV0TheoryConstructionBoundedProgramPreparationResultReview.theoremAttempted = false ∧
    Derivation.ToeCCFTV0TheoryConstructionBoundedProgramPreparationAuthority.proposalPreparationAuthorized = true := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
