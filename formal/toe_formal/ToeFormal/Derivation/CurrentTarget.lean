import ToeFormal.Derivation.DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessInstrumentedR13MechanismExperimentNumericalFreezePacketV1

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
  DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessInstrumentedR13MechanismExperimentNumericalFreezePacketV1.selectedNextTarget

def currentEvidencePacketId : String :=
  DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessInstrumentedR13MechanismExperimentNumericalFreezePacketV1.packetId

theorem current_target_selects_independent_instrumented_R13_numerical_freeze_v1_review :
    currentLiveTarget =
      "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_numerical_freeze_packet_v1_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
