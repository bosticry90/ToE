import ToeFormal.Derivation.CCFTSCQEDLiteratureApplicabilityMatrixCalculationSprintGuardrailPacket

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
  CCFTSCQEDLiteratureApplicabilityMatrixCalculationSprintGuardrailPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  CCFTSCQEDLiteratureApplicabilityMatrixCalculationSprintGuardrailPacket.packetId

theorem current_target_points_to_ccft_scqed_literature_applicability_matrix_calculation_execution :
    currentLiveTarget =
      "execute_calc_ccft_scqed_literature_applicability_matrix_v0" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
