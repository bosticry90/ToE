/-
ToeFormal/SubstrateToyLaws/RegimeSwitching.lean

Family D — Regime / Phase Switching (STRUCTURE ONLY)

This file defines a regime selector and switching wrapper for candidate laws.
No physical meaning is asserted here.

Admissibility predicates for any candidate are defined and enforced only in the
Python consequence-engine lane via bounded, deterministic tests.
-/

import ToeFormal.SubstrateToyLaws.ViabilityFlow

namespace ToeFormal
namespace SubstrateToyLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- `CandidateLaw` and `Gates` are the shared structural definitions imported
from `ViabilityFlow`; this module must not redeclare the same namespace names. -/

/-- Regime label: two-mode switching scaffold. -/
inductive Regime where
  | coherent
  | incoherent
deriving DecidableEq, Repr

/-- Order parameter for regime selection (structure only). -/
abbrev OrderParam (S : Type) := SubstrateState S -> ℝ

/-- A regime selector is a threshold rule over an order parameter. -/
structure RegimeSelector (S : Type) where
  μ    : OrderParam S
  μc   : ℝ
  /-- Selection rule; you may replace with a different (still structural) definition later. -/
  select : SubstrateState S -> Regime :=
    fun s => if μ s > μc then Regime.coherent else Regime.incoherent

/-- Family D wrapper: choose between two candidate laws based on the selected regime. -/
def switchedLaw {S : Type} (sel : RegimeSelector S) (lawC lawI : CandidateLaw S) : CandidateLaw S :=
  fun s =>
    match sel.select s with
    | Regime.coherent   => lawC s
    | Regime.incoherent => lawI s

/-- A placeholder selector instance parameterized by μ and μc (no claims). -/
noncomputable def selectorD1 {S : Type} (μ : OrderParam S) (μc : ℝ) : RegimeSelector S :=
  { μ := μ, μc := μc }

end SubstrateToyLaws
end ToeFormal
