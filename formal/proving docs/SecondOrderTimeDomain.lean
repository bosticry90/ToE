import Mathlib

namespace ToeFormal
namespace UCFF

noncomputable section
set_option autoImplicit false

-- LOCK_SECOND_ORDER_TIME_DOMAIN.md
-- Canonical module + objects (documentation lock; not an implementation lock):
--   equations/phase13_ucff_second_order.py
--     second_order_eom_phi()
--     second_order_dispersion_from_eom()
--     second_order_dispersion_natural_units_from_eom()
--     symbol_names_phase13_second_order()
--
-- Canonical requirements from the lock:
--   • time-domain residual-form equation contains φ_tt and spatial derivatives up to 6th order
--   • nonlinearity appears in explicit density form g*(conj(phi)*phi)*phi
--   • dispersion objects are presented in ω²(k) form with k²/k⁴/k⁶ present
--     and parameters (lam, beta) present
--   • "natural units" presentation removes explicit hbar and m

-- Complex scalar field φ(t,x).
abbrev Field : Type := ℝ → ℝ → ℂ

-- Abstract derivative operators (structural placeholders in this lock layer).
opaque Dtt : Field → Field
opaque Dxx : Field → Field
opaque Dxxxx : Field → Field
opaque Dxxxxxx : Field → Field

-- Explicit density-form nonlinearity: g * (conj(phi) * phi) * phi (pointwise).
-- In Lean/Mathlib, complex conjugation is `star` on ℂ.
def cubicDensity (g : ℝ) (phi : Field) : Field :=
  fun t x =>
    (g : ℂ) * (star (phi t x) * (phi t x)) * (phi t x)

-- Canonical residual-form EOM object (structural).
def secondOrderTimeDomainResidual (g lam beta : ℝ) (phi : Field) : Field :=
  fun t x =>
      (Dtt phi t x)
    + ((1 : ℂ) / (2 : ℂ)) * (Dxx phi t x)
    - (lam : ℂ) * (Dxxxx phi t x)
    - (beta : ℂ) * (Dxxxxxx phi t x)
    + (cubicDensity g phi t x)

-- “Residual-form canon”: residual = 0.
def SatisfiesSecondOrderTimeDomain (g lam beta : ℝ) (phi : Field) : Prop :=
  ∀ t x : ℝ, secondOrderTimeDomainResidual g lam beta phi t x = 0

theorem secondOrderTimeDomainResidual_expand
    (g lam beta : ℝ) (phi : Field) (t x : ℝ) :
    secondOrderTimeDomainResidual g lam beta phi t x
      =
      (Dtt phi t x)
    + ((1 : ℂ) / (2 : ℂ)) * (Dxx phi t x)
    - (lam : ℂ) * (Dxxxx phi t x)
    - (beta : ℂ) * (Dxxxxxx phi t x)
    + (cubicDensity g phi t x) := by
  rfl

-- ω²(k) dispersion objects (structural shape lock).
-- The lock requires: ω²(k) form with explicit k², k⁴, k⁶ present and parameters lam, beta present.
-- Do NOT lock exact coefficients here (physics/derivation lives in Python locks/tests).
def omegaSqSecondOrder (g rho0 a4 lam beta : ℝ) (k : ℝ) : ℝ :=
  (g * rho0) * k ^ 2 + (a4 + lam) * k ^ 4 + beta * k ^ 6

theorem omegaSqSecondOrder_expand
    (g rho0 a4 lam beta : ℝ) (k : ℝ) :
    omegaSqSecondOrder g rho0 a4 lam beta k
      =
      (g * rho0) * k ^ 2 + (a4 + lam) * k ^ 4 + beta * k ^ 6 := by
  rfl

-- Natural-units ω²(k) object (structural):
-- lock requires explicit hbar/m not appear in RHS; we bind them to avoid unused-variable lints.
def omegaSqSecondOrderNaturalUnits (hbar m c g rho0 a4 lam beta : ℝ) (k : ℝ) : ℝ :=
  let _ := hbar
  let _ := m
  let _ := c
  omegaSqSecondOrder g rho0 a4 lam beta k

theorem omegaSqSecondOrderNaturalUnits_expand
    (hbar m c g rho0 a4 lam beta : ℝ) (k : ℝ) :
    omegaSqSecondOrderNaturalUnits hbar m c g rho0 a4 lam beta k
      =
      omegaSqSecondOrder g rho0 a4 lam beta k := by
  rfl


end
end UCFF
end ToeFormal
