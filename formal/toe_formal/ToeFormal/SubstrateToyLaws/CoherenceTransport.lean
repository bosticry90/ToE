/-
ToeFormal/SubstrateToyLaws/CoherenceTransport.lean

STRUCTURE-ONLY MODULE.
This file defines abstract interfaces for a "coherence transport" toy-law family.
No physical meaning is asserted. Predicates are admissibility gates only.
Python implementations, if any, are consequence-engine checks against these interfaces.
-/

namespace ToeFormal
namespace SubstrateToyLaws

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Abstract substrate state type. Keep opaque at this layer. -/
constant SubstrateState : Type u

/-- Abstract coherence carrier type (could later be scalar field, measure, etc.). -/
constant CoherenceState : Type u

/-- Combined toy state for Family B. -/
structure BState where
  substrate : SubstrateState
  coherence : CoherenceState

/-- Abstract parameter bundle for a Family B candidate law. -/
structure BParams where
  -- Intentionally empty for now; add knobs only when needed.
  dummy : Unit := ()

/-- Candidate law: deterministic step form. -/
abbrev CandidateLawB := BParams -> BState -> BState

/-- Admissibility predicate (structural gate only; no physical meaning). -/
abbrev AdmissibleB := BParams -> BState -> Prop

/-- Optional gate wrapper for CT/SYM/CAUS-style predicates. -/
structure GatePack (α : Type u) where
  CT   : α -> Prop
  SYM  : α -> Prop
  CAUS : α -> Prop

/-- One minimal “instance” placeholder: a named candidate with its admissibility gate. -/
structure CandidateB where
  name       : String
  params     : BParams
  step       : CandidateLawB
  admissible : AdmissibleB

/-- Minimal structural placeholder candidate (identity step, trivial admissibility). -/
def defaultBParams : BParams := { dummy := () }

def candidateIdentity : CandidateB :=
  {
    name := "B0_identity",
    params := defaultBParams,
    step := fun _ s => s,
    admissible := fun _ _ => True,
  }

/-- Minimal structural placeholder candidate (transport proxy placeholder). -/
def candidateTransportProxy : CandidateB :=
  {
    name := "B2_transport_proxy",
    params := defaultBParams,
    step := fun _ s => s,
    admissible := fun _ _ => True,
  }

end SubstrateToyLaws
end ToeFormal
