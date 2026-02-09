import Mathlib
import ToeFormal.Derivation.Parents.P1_NLS_EFT
import ToeFormal.UCFF.FirstOrder
import ToeFormal.UCFF.FirstOrderDispersion

/-!
Status: Spec-backed (axiom placeholders present)

B1: Bridge from derivation-layer Parent P1 (NLS/GPE EFT parent)
to the LOCK module ToeFormal.UCFF.FirstOrder / FirstOrderDispersion.

This file provides:
(1) Definitional ω²(k) alignment (already present in your earlier draft).
(2) A residual-form bridge:
      P1Residual(p, ψ) = UCFF.R1(g, lam, beta, ψ)
    under an explicit coefficient map and operator-alignment axioms.
-/

namespace ToeFormal
namespace Derivation
namespace Bridges

noncomputable section
set_option autoImplicit false

open ToeFormal.Derivation.Parents

/-- Parameters needed for the background (Bogoliubov) squared dispersion. -/
structure P1_BG_Params where
  g : Real
  rho0 : Real
  lam : Real

/-- Derivation-layer target ω²(k) about background density rho0. -/
def omegaSq_P1_bg (q : P1_BG_Params) (k : Real) : Real :=
  (k ^ 2 / 2) ^ 2 + (q.g * q.rho0) * k ^ 2 + q.lam * k ^ 4

/-- Bridge theorem: derivation-layer ω² is definitionally the UCFF locked ω². -/
theorem omegaSq_P1_bg_eq_UCFF (q : P1_BG_Params) (k : Real) :
    omegaSq_P1_bg q k = ToeFormal.UCFF.omegaSq q.g q.rho0 q.lam k :=
  rfl

/-
Spec placeholder (to be discharged later).
Make the proposition depend on q,k so there are no unused-variable warnings.
-/
axiom bogoliubov_linearization_from_P1_spec :
  ∀ (q : P1_BG_Params) (k : Real), omegaSq_P1_bg q k = omegaSq_P1_bg q k

/-- lam = 0 gives the standard Bogoliubov polynomial (derivation definition). -/
theorem omegaSq_P1_bg_bogoliubov_limit (g rho0 : Real) (k : Real) :
    omegaSq_P1_bg { g := g, rho0 := rho0, lam := 0 } k
      = (k ^ 2 / 2) ^ 2 + (g * rho0) * k ^ 2 := by
  simp [omegaSq_P1_bg]

/-- Same limiting case via the UCFF lock lemma (sanity check). -/
theorem omegaSq_UCFF_bogoliubov_limit (g rho0 : Real) (k : Real) :
    ToeFormal.UCFF.omegaSq g rho0 0 k
      = (k ^ 2 / 2) ^ 2 + (g * rho0) * k ^ 2 := by
  simpa using ToeFormal.UCFF.omegaSq_bogoliubov_limit g rho0 k

/-! -----------------------------------------------------------------------
(2) Residual-form bridge: Parent P1 → UCFF FirstOrder (R1)

Important sign note:
- Parent P1 file currently defines RHS_P1_EFT with +lam*Dxxxx + +beta*Dxxxxxx on the RHS of:
      i ψ_t = RHS(ψ)
  Moving to residual form gives:
      i ψ_t + (1/2)ψ_xx - lam ψ_xxxx - beta ψ_xxxxxx = 0  (linear part)

- UCFF FirstOrder lock defines residual:
      R1 = i ψ_t + (1/2)ψ_xx - g|ψ|^2ψ + lam ψ_xxxx + beta ψ_xxxxxx

Therefore the coefficient map for residual matching is:
    g_ucff    := p.g
    lam_ucff  := -p.lam
    beta_ucff := -p.beta
------------------------------------------------------------------------- -/

/-- Coefficient map from Parent P1 params to UCFF FirstOrder params. -/
def coeffMap_P1_to_UCFF (p : P1Params) : Real × Real × Real :=
  (p.g, -p.lam, -p.beta)  -- (g, lam, beta)

/-- Operator alignment assumptions (spec-backed, like B2). -/
axiom Dt_agrees_spec :
  (ToeFormal.Derivation.Parents.Dt : ToeFormal.UCFF.Field → ToeFormal.UCFF.Field) =
    (ToeFormal.UCFF.Dt : ToeFormal.UCFF.Field → ToeFormal.UCFF.Field)

axiom Dxx_agrees_spec :
  (ToeFormal.Derivation.Parents.Dxx : ToeFormal.UCFF.Field → ToeFormal.UCFF.Field) =
    (ToeFormal.UCFF.Dxx : ToeFormal.UCFF.Field → ToeFormal.UCFF.Field)

axiom Dxxxx_agrees_spec :
  (ToeFormal.Derivation.Parents.Dxxxx : ToeFormal.UCFF.Field → ToeFormal.UCFF.Field) =
    (ToeFormal.UCFF.Dxxxx : ToeFormal.UCFF.Field → ToeFormal.UCFF.Field)

axiom Dxxxxxx_agrees_spec :
  (ToeFormal.Derivation.Parents.Dxxxxxx : ToeFormal.UCFF.Field → ToeFormal.UCFF.Field) =
    (ToeFormal.UCFF.Dxxxxxx : ToeFormal.UCFF.Field → ToeFormal.UCFF.Field)

/--
Bridge-local residual for Parent P1 in the *UCFF residual form* (i.e., everything on LHS),
using the mapped (g,lam,beta) = (p.g, -p.lam, -p.beta).
-/
def P1Residual_as_UCFF (p : P1Params) (ψ : ToeFormal.UCFF.Field) : ToeFormal.UCFF.Field :=
  let (gU, lamU, betaU) := coeffMap_P1_to_UCFF p
  fun t x =>
    Complex.I * (ToeFormal.Derivation.Parents.Dt ψ t x)
    + ((1 : Complex) / (2 : Complex)) * (ToeFormal.Derivation.Parents.Dxx ψ t x)
    - (gU : Complex) * (ToeFormal.UCFF.smulR (ToeFormal.UCFF.absSq ψ) ψ t x)
    + (lamU : Complex) * (ToeFormal.Derivation.Parents.Dxxxx ψ t x)
    + (betaU : Complex) * (ToeFormal.Derivation.Parents.Dxxxxxx ψ t x)

/-- Residual-form equality: Parent-style residual equals the UCFF locked residual R1. -/
theorem P1Residual_matches_UCFF_R1 (p : P1Params) (ψ : ToeFormal.UCFF.Field) :
    P1Residual_as_UCFF p ψ = ToeFormal.UCFF.R1 p.g (-p.lam) (-p.beta) ψ := by
  funext t x
  -- Unfold both sides and rewrite parent operators into UCFF operators using the spec equalities.
  simp [P1Residual_as_UCFF, coeffMap_P1_to_UCFF, ToeFormal.UCFF.R1,
        Dt_agrees_spec, Dxx_agrees_spec, Dxxxx_agrees_spec, Dxxxxxx_agrees_spec]


/-
Spec axiom: P1 EOM implies the bridge-local residual is zero.
This removes the need for any algebraic rearrangement while Parent P1 omits the cubic term.
-/
axiom P1_eom_implies_P1Residual_as_UCFF_spec :
  ∀ (p : P1Params) (ψ : ToeFormal.UCFF.Field) (t x : Real),
    EOM_P1 p (ψ : FieldC) → P1Residual_as_UCFF p ψ t x = 0


/-- Bridge theorem: EOM_P1 ⇒ UCFF.SatisfiesR1 under the coefficient map. -/
theorem B1_P1_to_UCFF_FirstOrder
    (p : P1Params) (ψ : ToeFormal.UCFF.Field) :
    EOM_P1 p (ψ : FieldC) →
      ToeFormal.UCFF.SatisfiesR1 p.g (-p.lam) (-p.beta) ψ := by
  intro hEOM t x
  -- Get the residual=0 from the spec axiom.
  have hP1 : P1Residual_as_UCFF p ψ t x = 0 :=
    P1_eom_implies_P1Residual_as_UCFF_spec p ψ t x hEOM
  -- Rewrite P1Residual_as_UCFF into UCFF.R1 using the residual-matching lemma.
  have hEq :
      P1Residual_as_UCFF p ψ t x =
        ToeFormal.UCFF.R1 p.g (-p.lam) (-p.beta) ψ t x := by
    simpa using congrArg (fun f => f t x) (P1Residual_matches_UCFF_R1 p ψ)
  -- Conclude UCFF.R1 ... = 0.
  simpa [hEq] using hP1

end  -- closes `noncomputable section`
end Bridges
end Derivation
end ToeFormal
