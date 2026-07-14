import ToeFormal.Derivation.PillarSeamUnitMappingLedgerBlockerResponseRouteSelectionPacketV2ResultReview

namespace ToeFormal
namespace Derivation
namespace PillarSeamUnitMappingLedgerFirstUnitSelectorPacket

def packetId : String :=
  "PILLAR_SEAM_UNIT_MAPPING_LEDGER_FIRST_UNIT_SELECTOR_PACKET_v0"

def target : String :=
  PillarSeamUnitMappingLedgerBlockerResponseRouteSelectionPacketV2ResultReview.selectedNextTarget

def selectedNextTarget : String :=
  "review_pillar_seam_unit_mapping_ledger_first_unit_selector_packet_v0_result"

def postAcceptanceTarget : String :=
  "prepare_maxwell_dirac_unit_object_foundation_packet_v0"

def generatorSha256 : String :=
  "91a224102775972c1ff43a544ae1e0acd67cd8b6d962dd1249a62b72a41ebb5b"

def packetSha256 : String :=
  "2441f3e766f4546ef31530ff2ca00b79251591e868226ff7e41b1ad3b4d12375"

def manifestSha256 : String :=
  "b8b4554a1e9f134c6e83c64eb4e6770fadf53e4acd3aef9c7884626743447b6e"

def reportSha256 : String :=
  "afb502f24ab74a99104dab130ff26256a31dc8e5444f72fe3575c18eceb175a3"

def selectedPillarCode : String := "SR"
def selectedRowId : String := "PILLAR-SR-units_and_dimensions-v0"
def selectedWeightedScore : Nat := 51
def maximumWeightedScore : Nat := 62
def targetSelectionThreshold : Nat := 44
def sensitivityThresholdCount : Nat := 5
def criterionCount : Nat := 8
def scoredRowCount : Nat := 7

def thresholdSensitive : Bool := false
def targetSelectionReady : Bool := true
def resolutionExecutionReady : Bool := false
def selectionAuthorizesPreparationOnly : Bool := true
def unitAssignmentAuthorized : Bool := false
def restorationRuleAuthorized : Bool := false
def MaxwellDiracSelected : Bool := false
def cKActionEmbeddingAuthorized : Bool := false
def ccftResumed : Bool := false
def masterActionPromoted : Bool := false

theorem selector_consumes_exact_review_successor :
    target =
      "prepare_pillar_seam_unit_mapping_ledger_first_unit_selector_packet_v0" := by
  rfl

theorem selector_records_exact_scoring_surface :
    scoredRowCount = 7 ∧ criterionCount = 8 ∧
      maximumWeightedScore = 62 ∧ targetSelectionThreshold = 44 ∧
      sensitivityThresholdCount = 5 := by
  decide

theorem selector_selects_sr_for_preparation_only :
    selectedPillarCode = "SR" ∧
      selectedRowId = "PILLAR-SR-units_and_dimensions-v0" ∧
      selectedWeightedScore = 51 ∧ thresholdSensitive = false ∧
      targetSelectionReady = true ∧ resolutionExecutionReady = false ∧
      selectionAuthorizesPreparationOnly = true := by
  decide

theorem selector_emits_no_unit_or_downstream_promotion :
    unitAssignmentAuthorized = false ∧ restorationRuleAuthorized = false ∧
      MaxwellDiracSelected = false ∧ cKActionEmbeddingAuthorized = false ∧
      ccftResumed = false ∧ masterActionPromoted = false := by
  decide

end PillarSeamUnitMappingLedgerFirstUnitSelectorPacket
end Derivation
end ToeFormal
