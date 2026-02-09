import Mathlib

namespace ToeFormal
namespace UCFF

noncomputable section
set_option autoImplicit false

-- LOCK_FOUNDATION_FIRST_ORDER.md
-- Canonical source: equations/ucff_core.py :: ucff_first_order_eom()
--
-- R1[phi] = i phi_t + (1/2) phi_xx - g|phi|^2 phi + lam phi_xxxx + beta phi_xxxxxx = 0

-- Field phi(t,x) as a complex-valued function of (time, space).
abbrev Field : Type := Real -> Real -> Complex

-- Abstract derivative operators (structural placeholders in this milestone).
opaque Dt : Field → Field
opaque Dxx : Field → Field
opaque Dxxxx : Field → Field
opaque Dxxxxxx : Field → Field

-- Pointwise squared magnitude |phi|^2.
def absSq (phi : Field) : Real -> Real -> Real :=
  fun t x => Complex.normSq (phi t x)

-- Multiply a real-valued coefficient function with a field (pointwise).
def smulR (a : Real -> Real -> Real) (phi : Field) : Field :=
  fun t x => (a t x : Complex) * (phi t x)

-- First-order UCFF residual operator (structural lock).
def R1 (g lam beta : Real) (phi : Field) : Field :=
  fun t x =>
    Complex.I * (Dt phi t x)
    + ((1 : Complex) / (2 : Complex)) * (Dxx phi t x)
    - (g : Complex) * (smulR (absSq phi) phi t x)
    + (lam : Complex) * (Dxxxx phi t x)
    + (beta : Complex) * (Dxxxxxx phi t x)

-- "R1[phi] = 0" as a proposition.
def SatisfiesR1 (g lam beta : Real) (phi : Field) : Prop :=
  forall t x : Real, R1 g lam beta phi t x = 0

-- Expansion lemma: R1 at a point is exactly the locked sum of terms.
theorem R1_expand (g lam beta : Real) (phi : Field) (t x : Real) :
    R1 g lam beta phi t x =
      Complex.I * (Dt phi t x)
    + ((1 : Complex) / (2 : Complex)) * (Dxx phi t x)
    - (g : Complex) * (smulR (absSq phi) phi t x)
    + (lam : Complex) * (Dxxxx phi t x)
    + (beta : Complex) * (Dxxxxxx phi t x) := by
  rfl

-- GPE limit (structural): lam = 0 and beta = 0.
theorem R1_gpe_limit (g : Real) (phi : Field) (t x : Real) :
    R1 g 0 0 phi t x =
      Complex.I * (Dt phi t x)
    + ((1 : Complex) / (2 : Complex)) * (Dxx phi t x)
    - (g : Complex) * (smulR (absSq phi) phi t x) := by
  simp [R1, smulR, absSq]

end
end UCFF
end ToeFormal