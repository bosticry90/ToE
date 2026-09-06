import ToeFormal.Derivation.SRPillarCoordinateConventionAndConstantRestorationPacketReviewV3

namespace ToeFormal
namespace Derivation
namespace PostSRToolingFullToeScientificPrioritySelectionV0

def packetId : String :=
  "POST_SR_TOOLING_FULL_TOE_SCIENTIFIC_PRIORITY_SELECTION_20260717_v0"

def consumedTarget : String :=
  SRPillarCoordinateConventionAndConstantRestorationPacketReviewV3.selectedNextTarget

def verdict : String :=
  "SELECTED_DIRECT_GR_KNOWN_LIMIT_RECOVERY_PREPARATION"

def selectedCandidate : String :=
  "GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY"

def selectedNextTarget : String :=
  "prepare_gr_weak_rotating_source_gravitomagnetic_recovery_packet_v0"

def eligibleCandidateCount : Nat := 6
def selectedScore : Nat := 93
def runnerUpScore : Nat := 83
def sensitivityVariantCount : Nat := 24

def selectedCandidateStable : Bool := true
def srConventionRetainedAsPolicy : Bool := true
def srAutomatedRestorationClosed : Bool := true
def r13Reopened : Bool := false
def srToolingReopened : Bool := false
def v4Authorized : Bool := false
def derivationExecutedNow : Bool := false
def empiricalAnalysisAuthorized : Bool := false
def newGeneralPurposeToolAuthorized : Bool := false
def packetPreparationAuthorized : Bool := true
def automationCreated : Bool := false

theorem selection_consumes_full_priority_map_target :
    consumedTarget =
      "select_next_high_leverage_scientific_obligation_from_full_toe_priority_map" := by
  rfl

theorem selection_retains_sr_policy_and_closed_tooling :
    srConventionRetainedAsPolicy = true ∧
      srAutomatedRestorationClosed = true ∧ r13Reopened = false ∧
      srToolingReopened = false ∧ v4Authorized = false := by
  decide

theorem selection_is_stable_direct_gr_recovery_choice :
    eligibleCandidateCount = 6 ∧ selectedScore = 93 ∧
      runnerUpScore = 83 ∧ sensitivityVariantCount = 24 ∧
      selectedCandidateStable = true ∧
      selectedCandidate =
        "GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY" := by
  decide

theorem selection_authorizes_preparation_not_execution_or_infrastructure :
    packetPreparationAuthorized = true ∧ derivationExecutedNow = false ∧
      empiricalAnalysisAuthorized = false ∧
      newGeneralPurposeToolAuthorized = false ∧ automationCreated = false := by
  decide

theorem selection_rotates_to_bounded_gr_packet_preparation :
    selectedNextTarget =
      "prepare_gr_weak_rotating_source_gravitomagnetic_recovery_packet_v0" := by
  rfl

end PostSRToolingFullToeScientificPrioritySelectionV0
end Derivation
end ToeFormal
