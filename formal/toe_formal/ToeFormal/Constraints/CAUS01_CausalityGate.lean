/-
CAUS-01 — Minimal Lean interface for structural causality / admissibility gates.

Purpose:
- Provide purely structural predicates corresponding to CAUS-01 gates:
  * no ψ-independent forcing (via designated zero)
  * locality (abstract, uninterpreted)
  * exclusion of elliptic-in-time behavior (abstract, uninterpreted)
  * time-order sanity (semantic tag parameterized by declared evolution form)

All gate predicates are semantic tags supplied by the caller.
No PDE theorems are proved here.
-/

import Mathlib

namespace ToeFormal
namespace Constraints
namespace CAUS01

universe u
variable {F : Type u}

/-- Declared evolution packaging (used only for sanity gating). -/
inductive EvolForm
  | firstOrderTime
  | secondOrderTime

/--
CAUS-01 — Minimal structural interface.

All gate predicates are *semantic tags supplied by the caller*.
No PDE theorems are proved here.
-/
structure CausalityGateSuite (F : Type u) where
  /-- Designated zero state used for "no forcing": P(0)=0. -/
  zero : F
  /-- Gate C3: locality under the project's CAUS-01 semantics. -/
  IsLocal : (F → F) → Prop
  /-- Gate C2: excludes "elliptic-in-time / acausal" structure under CAUS-01 semantics. -/
  NoEllipticInTime : (F → F) → Prop
  /--
  Gate C4: time-order sanity tag (semantic).
  Parameterized by declared evolution form to mirror CAUS-01 semantics.
  -/
  TimeOrderSane : EvolForm → (F → F) → Prop
  /-- Which evolution form this gate suite is intended to apply to. -/
  form : EvolForm

/-- Gate C1: no ψ-independent forcing (source-free admissibility). -/
def NoForcingAt (G : CausalityGateSuite F) (P : F → F) : Prop :=
  P G.zero = G.zero

/-- Gate C4 instantiated at the suite's declared evolution form. -/
def TimeOrderSaneAt (G : CausalityGateSuite F) (P : F → F) : Prop :=
  G.TimeOrderSane G.form P

/-- CAUS-01 admissibility: conjunction of gate predicates. -/
def CAUS01_Admissible (G : CausalityGateSuite F) (P : F → F) : Prop :=
  NoForcingAt G P ∧
  G.IsLocal P ∧
  G.NoEllipticInTime P ∧
  TimeOrderSaneAt G P

end CAUS01
end Constraints
end ToeFormal
