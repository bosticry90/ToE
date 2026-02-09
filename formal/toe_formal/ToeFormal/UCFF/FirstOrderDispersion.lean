import Mathlib

namespace ToeFormal
namespace UCFF

noncomputable section
set_option autoImplicit false

-- LOCK_FOUNDATION_FIRST_ORDER_DISPERSION.md
-- Canonical sources:
--   equations/ucff_core.py :: ucff_dispersion_first_order()
--   tests/test_ucff_core_symbolic.py
--   tests/test_phase31_gpe_limit.py
--   tests/test_ucff_core_roundtrip.py
--
-- Locked statement (dispersion, specified at the level of ω²(k)):
--   ω²(k) = (k²/2)² + (g ρ0) k² + lam k⁴

/-- Squared angular frequency ω²(k) for the first-order UCFF dispersion (locked form). -/
def omegaSq (g rho0 lam : Real) (k : Real) : Real :=
  (k^2 / 2)^2 + (g * rho0) * k^2 + lam * k^4

/-- Expansion lemma: ω²(k) is definitionally equal to the locked polynomial. -/
theorem omegaSq_expand (g rho0 lam : Real) (k : Real) :
    omegaSq g rho0 lam k = (k^2 / 2)^2 + (g * rho0) * k^2 + lam * k^4 := by
  rfl

-- Locked limiting case (standard Bogoliubov / NLS–GPE limit):
--   lam = 0, beta = 0, lambda_coh = 0  ⇒  ω²(k) = (k²/2)² + (g ρ0) k²
-- Note: beta and lambda_coh do not appear in omegaSq (absent at linear order).

theorem omegaSq_bogoliubov_limit (g rho0 : Real) (k : Real) :
    omegaSq g rho0 0 k = (k^2 / 2)^2 + (g * rho0) * k^2 := by
  simp [omegaSq]

end
end UCFF
end ToeFormal
