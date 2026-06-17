import ToeFormal.Derivation.MinimalGlobalToeMathematicalObligationIndexResultReview

/-
Lean marker for selecting the next global ToE work target from the minimal
mathematical obligation index. The selector chooses the QFT-GR weak-pairing
calculation packet and does not execute repair.
-/

namespace ToeFormal
namespace Derivation
namespace NextGlobalToeWorkTargetFromMathematicalObligationIndex

def selectionId : String :=
  "NEXT_GLOBAL_TOE_WORK_TARGET_FROM_MATHEMATICAL_OBLIGATION_INDEX_SELECTION_v0"

def outcomeId : String :=
  "NEXT_GLOBAL_TOE_WORK_TARGET_FROM_MATHEMATICAL_OBLIGATION_INDEX_SELECTS_" ++
    "QFT_GR_WEAK_PAIRING_CALCULATION_PACKET_WITH_NO_REPAIR_EXECUTION_OR_" ++
    "CLOSURE"

def consumedTarget : String :=
  "select_next_global_toe_work_target_from_mathematical_obligation_index"

def selectedNextTarget : String :=
  "prepare_qft_gr_source_action_test_action_weak_pairing_domain_" ++
    "calculation_packet"

def selectedTargetIsCalculationPacket : Bool := true
def selectedTargetExecutesRepair : Bool := false
def qftGRClosureClaimed : Bool := false
def masterActionPromoted : Bool := false

theorem selection_chooses_calculation_packet_only :
    selectedTargetIsCalculationPacket = true ∧
      selectedTargetExecutesRepair = false := by
  constructor <;> rfl

theorem selection_preserves_nonclosure :
    qftGRClosureClaimed = false ∧ masterActionPromoted = false := by
  constructor <;> rfl

end NextGlobalToeWorkTargetFromMathematicalObligationIndex
end Derivation
end ToeFormal
