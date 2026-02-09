/-
ToeFormal/SubstrateToyLaws/GaugeRedundancy.lean

STRUCTURE-ONLY MODULE.
This file defines abstract interfaces for a "gauge redundancy" toy-law family.
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
abbrev SubstrateStateH (S : Type) := SubstrateState S

/-- Candidate law: deterministic step form. -/
abbrev CandidateLawH (S : Type) := SubstrateStateH S -> SubstrateStateH S

/-- Gauge action on state space (structure only). -/
abbrev GaugeAction (G : Type) (S : Type) := G -> SubstrateStateH S -> SubstrateStateH S

/-- Local gauge parameters (structure only). -/
abbrev LocalGauge (I : Type) (G : Type) := I -> G

/-- Local gauge action on state space (structure only). -/
abbrev LocalGaugeAction (I : Type) (G : Type) (S : Type) := LocalGauge I G -> SubstrateStateH S -> SubstrateStateH S

/-- Equivalence relation induced by a gauge action (structure only). -/
abbrev EquivalentH (S : Type) := SubstrateStateH S -> SubstrateStateH S -> Prop

/-- Observable map (structure only). -/
abbrev ObservableH (S : Type) (O : Type) := SubstrateStateH S -> O

/-- Invariance predicate for an observable under a gauge action (structure only). -/
abbrev InvariantH (S : Type) := SubstrateStateH S -> Prop

/-- Admissibility predicate (structure only). -/
abbrev AdmissibleH (S : Type) := SubstrateStateH S -> Prop

/-- Optional gate wrapper for CT/SYM/CAUS-style predicates (structure only). -/
structure GatesH (S : Type) where
  CT   : AdmissibleH S
  SYM  : AdmissibleH S
  CAUS : AdmissibleH S

/-- Candidate record for gauge redundancy (structure only). -/
structure CandidateH (G : Type) (S : Type) (O : Type) where
  name       : String
  step       : CandidateLawH S
  action     : GaugeAction G S
  observable : ObservableH S O
  invariant  : InvariantH S
  admissible : AdmissibleH S

/-- Candidate record for local gauge redundancy (structure only). -/
structure CandidateH2 (I : Type) (G : Type) (S : Type) (O : Type) where
  name       : String
  step       : CandidateLawH S
  action     : LocalGaugeAction I G S
  observable : ObservableH S O
  invariant  : InvariantH S
  admissible : AdmissibleH S

/-- Gauge-equivalence induced by an action (structure only). -/
def gaugeEquivalent {G : Type} {S : Type} (action : GaugeAction G S) : EquivalentH S :=
  fun s1 s2 => ∃ g : G, action g s1 = s2

/-- Observable invariance predicate (structure only; no theorem asserted). -/
def ObservablesInvariant {G : Type} {S : Type} {O : Type}
  (action : GaugeAction G S) (obs : ObservableH S O) : InvariantH S :=
  fun s => ∀ g : G, obs (action g s) = obs s

/-- Observable invariance predicate for local gauge action (structure only; no theorem asserted). -/
def ObservablesInvariantLocal {I : Type} {G : Type} {S : Type} {O : Type}
  (action : LocalGaugeAction I G S) (obs : ObservableH S O) : InvariantH S :=
  fun s => ∀ g : LocalGauge I G, obs (action g s) = obs s

/-- Minimal structural candidate (invariant predicate + trivial admissibility). -/
def candidateH1 {G : Type} {S : Type} {O : Type}
  (step : CandidateLawH S) (action : GaugeAction G S) (obs : ObservableH S O) : CandidateH G S O :=
  {
    name := "H1_gauge_invariance",
    step := step,
    action := action,
    observable := obs,
    invariant := ObservablesInvariant action obs,
    admissible := fun _ => True,
  }

/-- Minimal structural local-gauge candidate (invariant predicate + trivial admissibility). -/
def candidateH2 {I : Type} {G : Type} {S : Type} {O : Type}
  (step : CandidateLawH S) (action : LocalGaugeAction I G S) (obs : ObservableH S O) : CandidateH2 I G S O :=
  {
    name := "H2_local_gauge_invariance",
    step := step,
    action := action,
    observable := obs,
    invariant := ObservablesInvariantLocal action obs,
    admissible := fun _ => True,
  }

end SubstrateToyLaws
end ToeFormal
