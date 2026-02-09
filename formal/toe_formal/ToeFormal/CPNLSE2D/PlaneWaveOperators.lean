/-
ToeFormal/CPNLSE2D/PlaneWaveOperators.lean

Phase A3: Operator-level inevitability lock for DR-01 in the linear Schrödinger limit (EQ-02).

Scope:
- Structural-only. No physical claims.
- No analytic development of derivatives in Mathlib.
- Uses opaque operators (Dt, Dxx, Dyy) on Field2D and assumes their action
  on the specific plane-wave template `planeWave` via the quarantined axioms:
    Dt_planeWave, Delta_planeWave
- Proves that EQ-02 on `planeWave` reduces to equality of the scalar coefficients
  multiplying `planeWave`, without cancellation.

Deliberate limitation:
- Extracting the scalar equality omega(kx,ky) = (kx^2 + ky^2)/2 from the reduced form
  requires a non-vanishing fact about `planeWave` (not assumed or proven here).

Robustness notes:
- Proofs avoid fragile coercion normalization between ℝ-division and ℂ-division by using
  an explicit complex coefficient `eigC`.
-/
import Mathlib
import ToeFormal.CPNLSE2D.PlaneWaveOperatorDefs
import ToeFormal.CPNLSE2D.PlaneWaveOperatorAxioms
import ToeFormal.Derivation.DR01_Redundant

namespace ToeFormal
namespace CPNLSE2D

noncomputable section
set_option autoImplicit false

/-- Helpful tiny lemma: -(I * (I * z)) = z for z : ℂ. -/
private lemma neg_I_I_mul (z : ℂ) : -(Complex.I * (Complex.I * z)) = z := by
  calc
    -(Complex.I * (Complex.I * z)) = -((Complex.I * Complex.I) * z) := by rw [mul_assoc]
    _ = -(-1 * z) := by rw [Complex.I_mul_I]
    _ = z := by simp

/-- Variant that handles an extra multiplicative factor on the right: -(I*(I*z)*w)=z*w. -/
private lemma neg_I_I_mul_mul (z w : ℂ) : -(Complex.I * (Complex.I * z) * w) = z * w := by
  rw [mul_assoc, mul_assoc]
  exact (neg_I_I_mul (z * w))

/-- Simplify (-(1/2)) * (-(K) * w) to (K/2) * w. -/
private lemma neg_div2_mul_neg_mul (K w : ℂ) :
  (-(1 : ℂ) / 2) * (-(K) * w) = (K / 2) * w := by
  simp [div_eq_mul_inv]
  ring

/-- Closed form for (i * Dt)(planeWave) using only the Dt_planeWave axiom. -/
theorem iDt_planeWave_closed (A : ℂ) (kx ky : ℝ) :
  (fun x y t => Complex.I * (Dt (planeWave A kx ky) x y t))
    =
    (fun x y t => ((omega kx ky : ℂ)) * (planeWave A kx ky x y t)) := by
  funext x y t
  calc
    Complex.I * (Dt (planeWave A kx ky) x y t)
        = Complex.I * ((-Complex.I * (omega kx ky : ℂ)) * (planeWave A kx ky x y t)) := by
          simpa using congrArg (fun f => Complex.I * f x y t) (Dt_planeWave A kx ky)
    _ = (omega kx ky : ℂ) * (planeWave A kx ky x y t) := by
          calc
            Complex.I * (-Complex.I * (omega kx ky : ℂ) * planeWave A kx ky x y t)
                = -(Complex.I * (Complex.I * ((omega kx ky : ℂ) * planeWave A kx ky x y t))) := by
                  simp [mul_assoc]
            _ = (omega kx ky : ℂ) * planeWave A kx ky x y t := by
                  exact (neg_I_I_mul ((omega kx ky : ℂ) * planeWave A kx ky x y t))

/-- Closed form for (-(1/2) * Delta)(planeWave) using only the Delta_planeWave axiom. -/
theorem negHalfDelta_planeWave_closed (A : ℂ) (kx ky : ℝ) :
  (fun x y t => (-(1 : ℂ) / 2) * (Delta (planeWave A kx ky) x y t))
    =
    (fun x y t => (eigC kx ky) * (planeWave A kx ky x y t)) := by
  funext x y t
  calc
    (-(1 : ℂ) / 2) * (Delta (planeWave A kx ky) x y t)
        = (-(1 : ℂ) / 2) * ( -((kx ^ 2 + ky ^ 2 : ℝ) : ℂ) * (planeWave A kx ky x y t)) := by
          simpa using congrArg (fun f => (-(1 : ℂ) / 2) * f x y t) (Delta_planeWave A kx ky)
    _ = (eigC kx ky) * (planeWave A kx ky x y t) := by
          simp [eigC, div_eq_mul_inv]
          ring

/-- Closed form for L(planeWave). -/
theorem L_planeWave_closed (A : ℂ) (kx ky : ℝ) :
  -- Delta_planeWave
  L (planeWave A kx ky)
    =
    fun x y t => (eigC kx ky) * (planeWave A kx ky x y t) := by
  funext x y t
  have h := congrArg (fun f => f x y t) (negHalfDelta_planeWave_closed A kx ky)
  simp [L, h]

/-- EQ-02 holds on planeWave iff the reduced scalar-coefficient forms match pointwise. -/
theorem EQ02Holds_planeWave_iff (A : ℂ) (kx ky : ℝ) :
  -- Dt_planeWave
  EQ02Holds (planeWave A kx ky)
    ↔
    (∀ x y t : ℝ,
      ((omega kx ky : ℂ)) * (planeWave A kx ky x y t)
        =
      (eigC kx ky) * (planeWave A kx ky x y t)) := by
  constructor
  · intro h x y t
    have hxy := h x y t
    have hL := congrArg (fun f => f x y t) (iDt_planeWave_closed A kx ky)
    have hR := congrArg (fun f => f x y t) (negHalfDelta_planeWave_closed A kx ky)
    calc
      (omega kx ky : ℂ) * (planeWave A kx ky x y t)
          = Complex.I * (Dt (planeWave A kx ky) x y t) := by exact Eq.symm hL
      _ = (-(1 : ℂ) / 2) * (Delta (planeWave A kx ky) x y t) := hxy
      _ = (eigC kx ky) * (planeWave A kx ky x y t) := hR
  · intro h x y t
    have hEq := h x y t
    have hL := congrArg (fun f => f x y t) (iDt_planeWave_closed A kx ky)
    have hR := congrArg (fun f => f x y t) (negHalfDelta_planeWave_closed A kx ky)
    calc
      Complex.I * (Dt (planeWave A kx ky) x y t)
          = (omega kx ky : ℂ) * (planeWave A kx ky x y t) := hL
      _ = (eigC kx ky) * (planeWave A kx ky x y t) := hEq
      _ = (-(1 : ℂ) / 2) * (Delta (planeWave A kx ky) x y t) := by
            exact Eq.symm hR

end
end CPNLSE2D
end ToeFormal
