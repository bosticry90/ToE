/-
ToeFormal/SubstrateToyLaws/StochasticSelection.lean

STRUCTURE-ONLY MODULE.
This file defines abstract interfaces for a "stochastic selection" toy-law family.
No physical meaning is asserted. Predicates are admissibility gates only.
Admissibility semantics are instantiated in Python bounded-evidence tests.
Front doors emit reports; tests define admissibility predicates and thresholds.
-/

import ToeFormal.SubstrateToyLaws.ViabilityFlow

namespace ToeFormal
namespace SubstrateToyLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Reuse the substrate state wrapper from the toy-law core. -/
abbrev SubstrateStateF (S : Type) := SubstrateState S

/-- Noise source: deterministic stream indexed by seed and step. -/
abbrev NoiseSource (Seed : Type) (Noise : Type) := Seed -> Nat -> Noise

/-- Stochastic step: state update given a noise draw. -/
abbrev StochasticStep (S : Type) (Noise : Type) := SubstrateStateF S -> Noise -> SubstrateStateF S

/-- Admissibility predicate (structure only). -/
abbrev AdmissibleF (S : Type) := SubstrateStateF S -> Prop

/-- Optional gate wrapper for CT/SYM/CAUS-style predicates (structure only). -/
structure GatesF (S : Type) where
  CT   : AdmissibleF S
  SYM  : AdmissibleF S
  CAUS : AdmissibleF S

/-- Candidate record for stochastic selection (structure only). -/
structure CandidateF (S : Type) (Seed : Type) (Noise : Type) where
  name       : String
  seed       : Seed
  noise      : NoiseSource Seed Noise
  step       : StochasticStep S Noise
  admissible : AdmissibleF S

/-- Placeholder candidate signature: seeded, step-indexed evolution. -/
abbrev CandidateF1 (S : Type) (Seed : Type) (Noise : Type) :=
  Seed -> Nat -> SubstrateStateF S -> SubstrateStateF S

/-- Structural placeholder: iterate step with a deterministic noise stream. -/
def candidateF1 {S : Type} {Seed : Type} {Noise : Type}
  (noise : NoiseSource Seed Noise)
  (step : StochasticStep S Noise) : CandidateF1 S Seed Noise :=
  fun seed n s =>
    Nat.rec (motive := fun _ => SubstrateStateF S)
      s
      (fun k acc => step acc (noise seed k))
      n

end SubstrateToyLaws
end ToeFormal
