import ToeFormal.Derivation.MinimalGlobalToeMathematicalObligationIndex

/-
Lean marker for the minimal mathematical obligation index result review.

The review accepts the index as selection support only and authorizes target
selection. It does not execute a repair or claim source admissibility.
-/

namespace ToeFormal
namespace Derivation
namespace MinimalGlobalToeMathematicalObligationIndexResultReview

def reviewId : String :=
  "MINIMAL_GLOBAL_TOE_MATHEMATICAL_OBLIGATION_INDEX_RESULT_REVIEW_v0"

def outcomeId : String :=
  "MINIMAL_GLOBAL_TOE_MATHEMATICAL_OBLIGATION_INDEX_RESULT_REVIEW_ACCEPTS_" ++
    "CALCULATION_FIRST_INDEX_AND_AUTHORIZES_SELECTION_ONLY"

def consumedTarget : String :=
  "review_minimal_global_toe_mathematical_obligation_index_result"

def selectedNextTarget : String :=
  "select_next_global_toe_work_target_from_mathematical_obligation_index"

def selectionOnlyAuthorized : Bool := true
def calculationPacketPreparedByThisReview : Bool := false
def sourceAdmissibilityClaimed : Bool := false
def qftGRClosureClaimed : Bool := false

theorem review_authorizes_selection_only :
    selectionOnlyAuthorized = true ∧
      calculationPacketPreparedByThisReview = false := by
  constructor <;> rfl

theorem review_preserves_qft_gr_nonclaims :
    sourceAdmissibilityClaimed = false ∧
      qftGRClosureClaimed = false := by
  constructor <;> rfl

end MinimalGlobalToeMathematicalObligationIndexResultReview
end Derivation
end ToeFormal
