/-
ToeFormal/SubstrateToyLaws/ScaleFlow.lean

STRUCTURE-ONLY MODULE.
This file defines abstract interfaces for a "scale-flow" toy-law family.
No physical meaning is asserted. Predicates are admissibility gates only.
Admissibility semantics are instantiated in Python bounded-evidence tests.
Front doors emit reports; tests define admissibility predicates and thresholds.
-/

import Mathlib

namespace ToeFormal
namespace SubstrateToyLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Scale parameter (structure only). -/
abbrev Scale := ℝ

/-- Coupling state (opaque carrier). -/
abbrev Couplings (G : Type) := G

/-- Beta function: g ↦ g (structure only). -/
abbrev BetaFn (G : Type) := Couplings G -> Couplings G

/-- Scale-step operator (structure only). -/
abbrev ScaleStep (G : Type) := (Δ : ℝ) -> BetaFn G -> Couplings G -> Couplings G

/-- Admissibility predicate over (scale, couplings). -/
abbrev AdmissibleE (G : Type) := Scale -> Couplings G -> Prop

/-- Optional gate wrapper for CT/SYM/CAUS-style predicates (structure only). -/
structure GatesE (G : Type) where
  CT   : AdmissibleE G
  SYM  : AdmissibleE G
  CAUS : AdmissibleE G

/-- Candidate record for scale-flow (structure only). -/
structure CandidateE (G : Type) where
  name       : String
  beta       : BetaFn G
  step       : ScaleStep G
  admissible : AdmissibleE G

/-- Linear beta placeholder (identity on the provided map). -/
def betaLinear {G : Type} (L : G -> G) : BetaFn G := L

section Euler

variable {G : Type}
variable [AddCommGroup G] [Module ℝ G]

/-- Euler-style scale step: g ↦ g + Δ • beta(g). -/
def scaleStepEuler : ScaleStep G :=
  fun Δ beta g => g + Δ • (beta g)

/-- Minimal structural candidate (Euler step + trivial admissibility). -/
def candidateEuler (beta : BetaFn G) : CandidateE G :=
  {
    name := "E1_euler",
    beta := beta,
    step := scaleStepEuler,
    admissible := fun _ _ => True,
  }

end Euler

end SubstrateToyLaws
end ToeFormal
