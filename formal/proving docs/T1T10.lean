import Mathlib

namespace ToeFormal
namespace LSDA

noncomputable section
set_option autoImplicit false

-- LOCK_LSDA_T1_T10.md
-- Scope: LSDA baseline code surface + tests T1–T10 (implementation + pytest enforcement + runner).
--
-- Locked equations / numerical form (as implemented):
--
-- Continuity (both RHS variants):
--   ∂t ρ = -∂x(ρ u)
--
-- Momentum (shared additive decomposition; dispersive sign differs by path):
--   ∂t u = (-u ∂x u) + (-g ∂x ρ) + (ν ∂xx u) + (dispersive term)
--
-- Dispersive sign divergence (implementation-level divergence recorded by the lock):
--   A) Finite-difference RHS (default integrate path: lsda/rk4.py → lsda/dynamics.py):
--        dispersive = -(λ ∂xxx ρ)
--   B) Spectral RHS (alternate path: lsda/stepper.py → lsda/eom.py):
--        dispersive = +(λ ∂xxx ρ)
--
-- This Lean file is a structural mirror: it locks the *forms* and the sign divergence.
-- It does not assert physical correctness beyond what tests compute and enforce.

-- Real scalar field f(t,x) on 1D periodic space with time.
abbrev FieldR : Type := ℝ → ℝ → ℝ

-- Abstract spatial derivative operators (structural placeholders).
opaque D1 : FieldR → FieldR   -- ∂x
opaque D2 : FieldR → FieldR   -- ∂xx
opaque D3 : FieldR → FieldR   -- ∂xxx

/-- Pointwise product of two real fields. -/
def mulRR (a b : FieldR) : FieldR :=
  fun t x => a t x * b t x

/-- Continuity RHS: ∂t ρ = -∂x(ρ u). -/
def drho (rho u : FieldR) : FieldR :=
  fun t x => - (D1 (mulRR rho u) t x)

-- Shared (sign-independent) momentum term decomposition:
--   du_adv  = -u * ∂x u
--   du_pres = -g * ∂x rho
--   du_visc =  nu * ∂xx u
def du_adv (u : FieldR) : FieldR :=
  fun t x => - (u t x) * (D1 u t x)

def du_pres (g : ℝ) (rho : FieldR) : FieldR :=
  fun t x => - g * (D1 rho t x)

def du_visc (nu : ℝ) (u : FieldR) : FieldR :=
  fun t x => nu * (D2 u t x)

-- Dispersive term variants (locked sign divergence):
--   FD path:  du_disp_fd   = -lam * ∂xxx rho
--   Spec path: du_disp_spec = +lam * ∂xxx rho
def du_disp_fd (lam : ℝ) (rho : FieldR) : FieldR :=
  fun t x => - lam * (D3 rho t x)

def du_disp_spec (lam : ℝ) (rho : FieldR) : FieldR :=
  fun t x => lam * (D3 rho t x)

/-- Full momentum RHS (finite-difference/default path). -/
def du_fd (g nu lam : ℝ) (rho u : FieldR) : FieldR :=
  fun t x =>
      du_adv u t x
    + du_pres g rho t x
    + du_visc nu u t x
    + du_disp_fd lam rho t x

/-- Full momentum RHS (spectral/alternate path). -/
def du_spec (g nu lam : ℝ) (rho u : FieldR) : FieldR :=
  fun t x =>
      du_adv u t x
    + du_pres g rho t x
    + du_visc nu u t x
    + du_disp_spec lam rho t x

-- Expansion lemmas (definitionally locked shapes).

theorem drho_expand (rho u : FieldR) (t x : ℝ) :
    drho rho u t x = - (D1 (mulRR rho u) t x) := by
  rfl

theorem du_fd_expand (g nu lam : ℝ) (rho u : FieldR) (t x : ℝ) :
    du_fd g nu lam rho u t x
      =
      (- (u t x) * (D1 u t x))
    + (- g * (D1 rho t x))
    + (nu * (D2 u t x))
    + (- lam * (D3 rho t x)) := by
  rfl

theorem du_spec_expand (g nu lam : ℝ) (rho u : FieldR) (t x : ℝ) :
    du_spec g nu lam rho u t x
      =
      (- (u t x) * (D1 u t x))
    + (- g * (D1 rho t x))
    + (nu * (D2 u t x))
    + (lam * (D3 rho t x)) := by
  rfl

-- Structural “system satisfied” predicates (optional, but keeps the lock style consistent).

def SatisfiesLSDA_FD (g nu lam : ℝ) (rho u : FieldR) (Drho Du : FieldR → FieldR) : Prop :=
  (Drho rho = drho rho u) ∧ (Du u = du_fd g nu lam rho u)

def SatisfiesLSDA_Spec (g nu lam : ℝ) (rho u : FieldR) (Drho Du : FieldR → FieldR) : Prop :=
  (Drho rho = drho rho u) ∧ (Du u = du_spec g nu lam rho u)

end
end LSDA
end ToeFormal
