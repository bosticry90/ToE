/-
ToeFormal/Variational/FNRepresentationEquivalencePolicy.lean

FN representation equivalence / quotient policy contract (structural-only).

Scope:
- Pins a policy token for cross-representation interpretability claims.
- Defines a generic quotient/equivalence contract for representation maps.
- Defines a comparator-side policy surface: invariant channels vs
  discriminative channels.
- No analytic claims; no physics truth-claim upgrade.
-/

import Mathlib

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-- Canonical token for FN representation-equivalence policy v1. -/
def fnRepPolicyToken : String := "FN_REP_EQ_POLICY_V1"

/-- Representation-equivalence contract for a state-to-representation map. -/
structure FNRepEquivalencePolicy (State Rep : Type) where
  encode : State -> Rep
  repEq : Rep -> Rep -> Prop
  repEq_refl : Reflexive repEq
  repEq_symm : Symmetric repEq
  repEq_trans : Transitive repEq

/-- Comparator-side policy: what must be invariant vs what may discriminate. -/
structure ComparatorRepPolicy (Rep : Type) where
  invariantUnder : Rep -> Rep -> Prop
  discriminativeOn : Rep -> Rep -> Prop

/-- A cross-representation interpretability claim is admissible iff it carries
the pinned policy token. -/
def crossRepClaimAllowed (policyToken claimToken : String) : Prop :=
  claimToken = policyToken

theorem cross_rep_claim_requires_policy_token
    (claimToken : String)
    (h : crossRepClaimAllowed fnRepPolicyToken claimToken) :
    claimToken = fnRepPolicyToken := h

end

end Variational
end ToeFormal
