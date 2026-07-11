/-
ToeFormal/SubstrateToyLaws/CoherenceTransport.lean

STRUCTURE-ONLY MODULE.
This file defines abstract interfaces for a "coherence transport" toy-law family.
No physical meaning is asserted. Predicates are admissibility gates only.
Python implementations, if any, are consequence-engine checks against these interfaces.
-/

import Mathlib

namespace ToeFormal
namespace SubstrateToyLaws

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Combined toy state for Family B. -/
structure BState (SubstrateState CoherenceState : Type u) where
  substrate : SubstrateState
  coherence : CoherenceState

/-- Abstract parameter bundle for a Family B candidate law. -/
structure BParams where
  -- Intentionally empty for now; add knobs only when needed.
  dummy : Unit := ()

/-- Candidate law: deterministic step form. -/
abbrev CandidateLawB (SubstrateState CoherenceState : Type u) :=
  BParams -> BState SubstrateState CoherenceState -> BState SubstrateState CoherenceState

/-- Admissibility predicate (structural gate only; no physical meaning). -/
abbrev AdmissibleB (SubstrateState CoherenceState : Type u) :=
  BParams -> BState SubstrateState CoherenceState -> Prop

/-- Optional gate wrapper for CT/SYM/CAUS-style predicates. -/
structure GatePack (α : Type u) where
  CT   : α -> Prop
  SYM  : α -> Prop
  CAUS : α -> Prop

/-- One minimal “instance” placeholder: a named candidate with its admissibility gate. -/
structure CandidateB (SubstrateState CoherenceState : Type u) where
  name       : String
  params     : BParams
  step       : CandidateLawB SubstrateState CoherenceState
  admissible : AdmissibleB SubstrateState CoherenceState

/-- Minimal structural placeholder candidate (identity step, trivial admissibility). -/
def defaultBParams : BParams := { dummy := () }

def candidateIdentity (SubstrateState CoherenceState : Type u) :
    CandidateB SubstrateState CoherenceState :=
  {
    name := "B0_identity",
    params := defaultBParams,
    step := fun _ s => s,
    admissible := fun _ _ => True,
  }

/-- Minimal structural placeholder candidate (transport proxy placeholder). -/
def candidateTransportProxy (SubstrateState CoherenceState : Type u) :
    CandidateB SubstrateState CoherenceState :=
  {
    name := "B2_transport_proxy",
    params := defaultBParams,
    step := fun _ s => s,
    admissible := fun _ _ => True,
  }

end SubstrateToyLaws
end ToeFormal
