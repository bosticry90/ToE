/-
ToeFormal/Variational/FNRep32Rep64Equivalence.lean

Rep32 <-> Rep64 equivalence target for FN-01 cubic lane surfaces
(structural-only, proof artifact for comparator interpretability policy).

Scope:
- Pins explicit transport maps between Rep32 and Rep64 lane aliases.
- Proves operator compatibility for EL and P_cubic on that transport.
- Proves cubic-lane equivalence (`EL = P_cubic`) across Rep32/Rep64 aliases.
- No analytic claims; no physics truth-claim upgrade.
-/

import Mathlib
import ToeFormal.Constraints.FN01_CandidateAPI
import ToeFormal.Variational.FNRepresentationEquivalencePolicy
import ToeFormal.Variational.DischargeELMatchesFN01Rep64Pcubic

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-- Canonical transport from Rep32 lane to Rep64 lane. -/
abbrev rep32ToRep64 : Field2DRep32 -> Field2DRep64 := fun x => x

/-- Canonical transport from Rep64 lane to Rep32 lane. -/
abbrev rep64ToRep32 : Field2DRep64 -> Field2DRep32 := fun x => x

theorem rep32_rep64_roundtrip_left (x : Field2DRep32) :
    rep64ToRep32 (rep32ToRep64 x) = x := rfl

theorem rep32_rep64_roundtrip_right (x : Field2DRep64) :
    rep32ToRep64 (rep64ToRep32 x) = x := rfl

theorem rep32_rep64_el_compat (x : Field2DRep32) :
    rep32ToRep64 (EL_toe_rep32 x) = EL_toe_rep64 (rep32ToRep64 x) := rfl

theorem rep32_rep64_pcubic_compat (g : ℂ) (x : Field2DRep32) :
    rep32ToRep64 (P_cubic_rep32 g x) = P_cubic_rep64 g (rep32ToRep64 x) := rfl

theorem rep32_rep64_fn01_cubic_equivalent :
    (EL_toe_rep32 = P_cubic_rep32 declared_g_rep32) <->
      (EL_toe_rep64 = P_cubic_rep64 declared_g_rep64) := by
  constructor
  · intro h
    simpa [EL_toe_rep64, P_cubic_rep64, declared_g_rep64] using h
  · intro h
    simpa [EL_toe_rep64, P_cubic_rep64, declared_g_rep64] using h

theorem rep32_rep64_cross_rep_claim_token_pinned :
    crossRepClaimAllowed fnRepPolicyToken "FN_REP_EQ_POLICY_V1" := by
  rfl

end

end Variational
end ToeFormal
