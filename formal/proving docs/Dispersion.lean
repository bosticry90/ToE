import Mathlib

namespace ToeFormal
namespace CPNLSE2D

noncomputable section
set_option autoImplicit false

-- LOCK_CP_NLSE_2D_DISPERSION.md
-- Canonical sources:
--   crft/tests/crft_c6_cp_nlse_2d_dispersion.py
--   crft/cp_nlse_2d.py
--   crft/__init__.py
--
-- Scope: linear Schrödinger limit only (g = 0).
--
-- Governing equation (operational 2D CP–NLSE):
--   i ∂t ψ = - (1/2) Δ ψ + g (|ψ|^2 - ρ0) ψ
-- where Δ = ∂xx + ∂yy.
--
-- Locked limiting case:
--   g = 0  ⇒  i ∂t ψ = - (1/2) Δ ψ
--
-- Locked plane-wave dispersion relation:
--   ω(kx, ky) = 1/2 (kx^2 + ky^2)

-- Field ψ(x,y,t) as a complex-valued function of (space, space, time).
abbrev Field2D : Type := ℝ → ℝ → ℝ → ℂ

/-- Angular frequency ω(kx, ky) for the 2D linear Schrödinger dispersion (locked form). -/
def omega (kx ky : ℝ) : ℝ :=
  (kx ^ 2 + ky ^ 2) / 2

/-- Expansion lemma: ω is definitionally equal to the locked expression. -/
theorem omega_expand (kx ky : ℝ) :
    omega kx ky = (kx ^ 2 + ky ^ 2) / 2 := by
  rfl

/-- Plane-wave ansatz ψ(x,y,t) = A * exp(i (kx x + ky y - ω t)). (Structural template.) -/
def planeWave (A : ℂ) (kx ky : ℝ) : Field2D :=
  fun x y t =>
    A * Complex.exp (Complex.I * ((kx * x + ky * y - (omega kx ky) * t) : ℂ))

-- Documentation-only reminders from the lock:
-- Validation procedure (C6):
--   - evolve plane wave with g = 0 on periodic 2π×2π grid (Nx=Ny=32),
--   - measure ω numerically from time series at grid point (0,0),
--   - check relative error < 1e-1.
--
-- This file locks only the dispersion formula ω(kx,ky) in the linear regime.

end
end CPNLSE2D
end ToeFormal
