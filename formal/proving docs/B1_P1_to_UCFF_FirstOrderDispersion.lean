import ToeFormal.Derivation.Parents.P1_NLS_EFT
import ToeFormal.UCFF.FirstOrderDispersion

namespace ToeFormal
namespace Derivation
namespace Bridges

noncomputable section
set_option autoImplicit false

open ToeFormal.Derivation.Parents

/-
B1: Bridge from derivation-layer Parent P1 (NLS/GPE EFT parent) to the LOCK module
ToeFormal.UCFF.FirstOrderDispersion.

Important:
- P1_NLS_EFT currently proves a *linear plane-wave dispersion* for the vacuum form:
      i ψ_t = -(1/2) ψ_xx + lam ψ_xxxx + beta ψ_xxxxxx
  which yields ω(k) = (1/2) k^2 + lam k^4 - beta k^6.

- UCFF.FirstOrderDispersion locks the *Bogoliubov squared frequency* about a constant
  background density ρ0:
      ω²(k) = (k²/2)² + (g ρ0) k² + lam k⁴.

These are not the same object. The UCFF dispersion is obtained by *linearizing the nonlinear
parent (with interaction g) around a nonzero background ρ0* and solving the resulting
2×2 mode system (u,v). That derivation is not formalized yet in Lean.

This bridge file therefore:
(1) fixes a parameter mapping,
(2) defines the derivation-layer target polynomial ω²_P1_bg that matches the lock,
(3) proves equivalence to the lock by definitional reduction,
(4) records the missing physics step as an explicit bridge axiom for later discharge.
-/

/-- Parameters needed for the background (Bogoliubov) dispersion. -/
structure P1_BG_Params where
  g    : ℝ
  rho0 : ℝ
  lam  : ℝ

/-- Map background-bridge params into Parent P1 params (beta set to 0 for this lock). -/
def toP1Params (q : P1_BG_Params) : P1Params :=
  { g := q.g, lam := q.lam, beta := 0 }

/--
Derivation-layer definition of the *background-linearized* squared dispersion for P1.

This is the target that should result from linearizing P1’s nonlinear dynamics about
ψ₀ with |ψ₀|² = rho0, producing the standard Bogoliubov form (plus the lam k⁴ EFT term).
-/
def omegaSq_P1_bg (q : P1_BG_Params) (k : ℝ) : ℝ :=
  (k^2 / 2)^2 + (q.g * q.rho0) * k^2 + q.lam * k^4

/-- Bridge theorem: the derivation-layer ω² polynomial is definitionally UCFF's locked ω². -/
theorem omegaSq_P1_bg_eq_UCFF (q : P1_BG_Params) (k : ℝ) :
    omegaSq_P1_bg q k = ToeFormal.UCFF.omegaSq q.g q.rho0 q.lam k := by
  rfl

/-
Physics/derivation obligation (to be proven later):

From Parent P1 (with nonlinear term restored), linearize around a constant background
density rho0 and show the perturbation modes satisfy the UCFF locked ω² polynomial.

We record this as an axiom at the bridge layer for now; later it should be discharged
by a formal linearization development (Derivation Layer E/F).
-/
axiom bogoliubov_linearization_from_P1 :
  ∀ (q : P1_BG_Params) (k : ℝ),
    True
    -- Placeholder for the future statement, e.g.:
    -- ∃ ω : ℝ, (LinearizedModeSolution (toP1Params q) q.rho0 k ω) ∧
    --         ω^2 = omegaSq_P1_bg q k

/-- Locked limiting case consistency: lam = 0 gives the standard Bogoliubov polynomial. -/
theorem omegaSq_P1_bg_bogoliubov_limit (g rho0 : ℝ) (k : ℝ) :
    omegaSq_P1_bg { g := g, rho0 := rho0, lam := 0 } k
      = (k^2 / 2)^2 + (g * rho0) * k^2 := by
  simp [omegaSq_P1_bg]

/-- Same statement but routed through the UCFF lock theorem (sanity check). -/
theorem omegaSq_UCFF_bogoliubov_limit (g rho0 : ℝ) (k : ℝ) :
    ToeFormal.UCFF.omegaSq g rho0 0 k = (k^2 / 2)^2 + (g * rho0) * k^2 := by
  simpa using ToeFormal.UCFF.omegaSq_bogoliubov_limit g rho0 k

end
end Bridges
end Derivation
end ToeFormal
