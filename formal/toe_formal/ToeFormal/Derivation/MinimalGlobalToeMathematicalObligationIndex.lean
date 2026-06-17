import ToeFormal.Derivation.QFTGRSourceMapLadderPacketFromCandidateSourceToAdmissibleSourceResultReview

/-
Lean marker for the minimal global ToE mathematical obligation index.

The index is a small calculation stoplight. It records what calculation is
required next and keeps the global maturity matrix deferred. It is not a
derivation artifact and does not claim theory closure.
-/

namespace ToeFormal
namespace Derivation
namespace MinimalGlobalToeMathematicalObligationIndex

def indexId : String :=
  "MINIMAL_GLOBAL_TOE_MATHEMATICAL_OBLIGATION_INDEX_v0"

def outcomeId : String :=
  "MINIMAL_GLOBAL_TOE_MATHEMATICAL_OBLIGATION_INDEX_PREPARED_WITH_NO_" ++
    "DERIVATION_EXECUTION_OR_THEORY_CLOSURE"

def consumedTarget : String :=
  "prepare_minimal_global_toe_mathematical_obligation_index"

def selectedNextTarget : String :=
  "review_minimal_global_toe_mathematical_obligation_index_result"

def qftGRFirstRequiredCalculation : String :=
  "construct_source_action_test_action_weak_pairing_domain"

def qftGRNextCalculationTarget : String :=
  "prepare_qft_gr_source_action_test_action_weak_pairing_domain_" ++
    "calculation_packet"

def qftGRFirstBreakRowId : String :=
  "source_action_test_action_and_weak_pairing_domain"

def unknownOrUnassessedStateAllowed : Bool := true
def globalMaturityMatrixDeferred : Bool := true
def calculationExecutedByThisIndex : Bool := false
def derivationExecutedByThisIndex : Bool := false
def theoryClosureClaimed : Bool := false
def publicHypothesisReadyClaimed : Bool := false

theorem index_is_support_not_derivation :
    calculationExecutedByThisIndex = false ∧
      derivationExecutedByThisIndex = false := by
  constructor <;> rfl

theorem index_records_qft_gr_next_calculation :
    qftGRFirstBreakRowId =
        "source_action_test_action_and_weak_pairing_domain" ∧
      qftGRFirstRequiredCalculation =
        "construct_source_action_test_action_weak_pairing_domain" := by
  constructor <;> rfl

theorem index_preserves_nonclosure :
    theoryClosureClaimed = false ∧
      publicHypothesisReadyClaimed = false := by
  constructor <;> rfl

end MinimalGlobalToeMathematicalObligationIndex
end Derivation
end ToeFormal
