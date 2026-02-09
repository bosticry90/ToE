import Mathlib

namespace ToeFormal
namespace UCFF

noncomputable section
set_option autoImplicit false

-- LOCK_SECOND_ORDER_NUMERICS.md
-- Scope: operational (numerics) first-order-in-time UCFF/UEFM evolution in 1D periodic geometry,
-- plus the locked linear dispersion ω(k) enforced by numerical tests.
--
-- Canonical implementation + tests (authoritative for this lock):
--   equations/phase13_second_order_numerics.py
--   tests/test_phase13_second_order_numerics.py
--   tests/test_phase13_second_order_cn_vs_splitstep.py
--   tests/test_phase13_second_order_mi.py
--
-- Locked operational PDE (exact documentation form):
--   i φ_t = - (1/2) φ_xx + lam φ_xxxx + beta φ_xxxxxx + g |φ|^2 φ
--
-- Locked linear dispersion (ω-form, not ω²-form), in the linear regime g = 0:
--   ω(k) = 0.5 k^2 + lam k^4 + beta k^6
--
-- Locked limiting case:
--   lam = 0 and beta = 0 reduces to standard NLS:
--     i φ_t = - (1/2) φ_xx + g |φ|^2 φ

-- Complex scalar field φ(t,x).
abbrev Field : Type := ℝ → ℝ → ℂ

-- Abstract derivative operators (structural placeholders in this lock layer).
opaque Dt      : Field → Field
opaque Dxx     : Field → Field
opaque Dxxxx   : Field → Field
opaque Dxxxxxx : Field → Field

-- Pointwise squared magnitude |φ|^2 (as a real-valued function).
def absSq (phi : Field) : ℝ → ℝ → ℝ :=
  fun t x => Complex.normSq (phi t x)

-- Multiply a real-valued coefficient function with a field (pointwise).
def smulR (a : ℝ → ℝ → ℝ) (phi : Field) : Field :=
  fun t x => (a t x : ℂ) * (phi t x)

-- Locked operational RHS:
--   RHS = - (1/2) φ_xx + lam φ_xxxx + beta φ_xxxxxx + g |φ|^2 φ
def secondOrderNumericsRHS (g lam beta : ℝ) (phi : Field) : Field :=
  fun t x =>
      - ((1 : ℂ) / (2 : ℂ)) * (Dxx phi t x)
    + (lam : ℂ) * (Dxxxx phi t x)
    + (beta : ℂ) * (Dxxxxxx phi t x)
    + (g : ℂ) * (smulR (absSq phi) phi t x)

-- Locked operational PDE written exactly in the lock’s documentation form:
--   i φ_t = RHS
def SatisfiesSecondOrderNumerics (g lam beta : ℝ) (phi : Field) : Prop :=
  ∀ t x : ℝ, (Complex.I * (Dt phi t x)) = secondOrderNumericsRHS g lam beta phi t x

-- Expansion lemma: definitionally the same RHS sum.
theorem secondOrderNumericsRHS_expand (g lam beta : ℝ) (phi : Field) (t x : ℝ) :
    secondOrderNumericsRHS g lam beta phi t x
      =
      - ((1 : ℂ) / (2 : ℂ)) * (Dxx phi t x)
    + (lam : ℂ) * (Dxxxx phi t x)
    + (beta : ℂ) * (Dxxxxxx phi t x)
    + (g : ℂ) * (smulR (absSq phi) phi t x) := by
  rfl

-- Locked limiting case: lam = beta = 0 gives the operational NLS RHS.
theorem secondOrderNumericsRHS_nls_limit (g : ℝ) (phi : Field) (t x : ℝ) :
    secondOrderNumericsRHS g 0 0 phi t x
      =
      - ((1 : ℂ) / (2 : ℂ)) * (Dxx phi t x)
    + (g : ℂ) * (smulR (absSq phi) phi t x) := by
  simp [secondOrderNumericsRHS, smulR, absSq]

-- Locked linear dispersion ω(k) in the linear regime (g = 0) for plane waves:
--   φ(x,t) = A exp(i (k x - ω t))
--   ω(k) = 0.5 k^2 + lam k^4 + beta k^6
def omega (lam beta : ℝ) (k : ℝ) : ℝ :=
  (1 / 2 : ℝ) * k^2 + lam * k^4 + beta * k^6

theorem omega_expand (lam beta : ℝ) (k : ℝ) :
    omega lam beta k = (1 / 2 : ℝ) * k^2 + lam * k^4 + beta * k^6 := by
  rfl

-- Locked dispersion limiting case: lam = beta = 0 ⇒ ω(k) = 0.5 k^2.
theorem omega_nls_limit (k : ℝ) :
    omega 0 0 k = (1 / 2 : ℝ) * k^2 := by
  simp [omega]

-- Structural plane-wave template used by tests (no PDE proof in this lock layer).
def planeWave (A : ℂ) (lam beta : ℝ) (k : ℝ) : Field :=
  fun t x =>
    A * Complex.exp (Complex.I * ((k * x - (omega lam beta k) * t) : ℂ))

-- Documentation-only reminders from the lock (not formalized here):
--   • Linear dispersion agreement: relative error < 1e-2 (ω estimated from time series, g = 0)
--   • Mass drift proxy: relative drift in M = ∫ |φ|^2 dx < 5e-2 (split-step)
--   • Split-step vs Crank–Nicolson agreement: relative L2 error < 1e-2 (linear regime g = 0)
--   • MI qualitative separation with beta > 0:
--       focusing: g < 0 shows strong growth (growth factor > 5.0)
--       defocusing: g > 0 remains comparatively stable (growth factor < 3.0)
--     (This is an operational sign convention enforced by tests.)

end
end UCFF
end ToeFormal
