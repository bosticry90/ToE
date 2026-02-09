/-
ToeFormal/SubstrateToyLaws/TopologicalInvariants.lean

STRUCTURE-ONLY MODULE.
This file defines abstract interfaces for a "topological invariants" toy-law family.
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
abbrev SubstrateStateG (S : Type) := SubstrateState S

/-- Candidate law: deterministic step form. -/
abbrev CandidateLawG (S : Type) := SubstrateStateG S -> SubstrateStateG S

/-- Defect/charge count (structure only). -/
abbrev DefectCount (S : Type) := SubstrateStateG S -> Nat

/-- Invariant predicate (structure only). -/
abbrev InvariantG (S : Type) := SubstrateStateG S -> Prop

/-- Admissibility predicate (structure only). -/
abbrev AdmissibleG (S : Type) := SubstrateStateG S -> Prop

/-- Optional gate wrapper for CT/SYM/CAUS-style predicates (structure only). -/
structure GatesG (S : Type) where
  CT   : AdmissibleG S
  SYM  : AdmissibleG S
  CAUS : AdmissibleG S

/-- Candidate record for topological invariants (structure only). -/
structure CandidateG (S : Type) where
  name       : String
  step       : CandidateLawG S
  defect     : DefectCount S
  invariant  : InvariantG S
  admissible : AdmissibleG S

/-- Defect conservation predicate (structure only; no theorem asserted). -/
def ConservesDefects {S : Type} (law : CandidateLawG S) (count : DefectCount S) : InvariantG S :=
  fun s => count (law s) = count s

/-- Minimal structural candidate (defect conservation + trivial admissibility). -/
def candidateG1 {S : Type} (law : CandidateLawG S) (count : DefectCount S) : CandidateG S :=
  {
    name := "G1_defect_conservation",
    step := law,
    defect := count,
    invariant := ConservesDefects law count,
    admissible := fun _ => True,
  }

end SubstrateToyLaws
end ToeFormal
