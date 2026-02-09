import Mathlib

namespace ToeFormal
namespace LCRD
namespace V3

noncomputable section
set_option autoImplicit false

-- LOCK_LCRD_V3_ROTOR_CURVATURE.md
-- Structural lock mirror of the numerical-layer lock:
-- Governing equations, coupling topology, first-order-in-time formulation,
-- and only D1 (∂x) and D2 (∂xx) operators appear.
--
-- Authoritative PDE system (1D periodic; spectral differentiation in numerics):
--
--   ∂t ρ = −∂x (ρ u)
--
--   ∂t u
--     = −u ∂x u
--       − g_eff ∂x ρ
--       + c1 ∂x R
--       + c2 ∂xx K
--       + nu_eff ∂xx u
--
--   ∂t R
--     = −alpha_R R
--       + b_R |∂x u|
--       + d_R ∂x K
--
--   ∂t K
--     = −alpha_K K
--       + b_K ∂x R

/-- Real scalar field f(t,x) on 1D space with time. -/
abbrev FieldR : Type := ℝ → ℝ → ℝ

-- Abstract spatial derivative operators (structural placeholders).
-- Numerically: spectral differentiation on a periodic grid (FFT multipliers).
opaque D1 : FieldR → FieldR   -- ∂x
opaque D2 : FieldR → FieldR   -- ∂xx

/-- Pointwise product of two real fields. -/
def mulRR (a b : FieldR) : FieldR :=
  fun t x => a t x * b t x

/-- Pointwise absolute value of a real field. -/
def absR (f : FieldR) : FieldR :=
  fun t x => |f t x|

/-- Locked RHS for density evolution: ∂t ρ = −∂x(ρ u). -/
def drho (rho u : FieldR) : FieldR :=
  fun t x => - (D1 (mulRR rho u) t x)

/-- Locked RHS for velocity evolution (LCRD v3). -/
def du (g_eff nu_eff c1 c2 : ℝ) (rho u R K : FieldR) : FieldR :=
  fun t x =>
      - (u t x) * (D1 u t x)
    - g_eff * (D1 rho t x)
    + c1 * (D1 R t x)
    + c2 * (D2 K t x)
    + nu_eff * (D2 u t x)

/-- Locked RHS for rotor evolution (LCRD v3). -/
def dR (alpha_R b_R d_R : ℝ) (u K R : FieldR) : FieldR :=
  fun t x =>
      - alpha_R * (R t x)
    + b_R * (absR (D1 u) t x)
    + d_R * (D1 K t x)

/-- Locked RHS for curvature evolution (LCRD v3). -/
def dK (alpha_K b_K : ℝ) (R K : FieldR) : FieldR :=
  fun t x =>
      - alpha_K * (K t x)
    + b_K * (D1 R t x)

/-- “Satisfies LCRD v3” as a first-order-in-time PDE system (structural). -/
def SatisfiesLCRDv3
    (g_eff nu_eff c1 c2 alpha_R alpha_K b_R b_K d_R : ℝ)
    (rho u R K : FieldR)
    (Drho Du DR DK : FieldR → FieldR) : Prop :=
  (Drho rho = drho rho u)
  ∧ (Du u = du g_eff nu_eff c1 c2 rho u R K)
  ∧ (DR R = dR alpha_R b_R d_R u K R)
  ∧ (DK K = dK alpha_K b_K R K)

-- Expansion lemmas (definitionally locked shapes).

theorem drho_expand (rho u : FieldR) (t x : ℝ) :
    drho rho u t x = - (D1 (mulRR rho u) t x) := by
  rfl

theorem du_expand (g_eff nu_eff c1 c2 : ℝ) (rho u R K : FieldR) (t x : ℝ) :
    du g_eff nu_eff c1 c2 rho u R K t x
      =
      - (u t x) * (D1 u t x)
    - g_eff * (D1 rho t x)
    + c1 * (D1 R t x)
    + c2 * (D2 K t x)
    + nu_eff * (D2 u t x) := by
  rfl

theorem dR_expand (alpha_R b_R d_R : ℝ) (u K R : FieldR) (t x : ℝ) :
    dR alpha_R b_R d_R u K R t x
      =
      - alpha_R * (R t x)
    + b_R * (absR (D1 u) t x)
    + d_R * (D1 K t x) := by
  rfl

theorem dK_expand (alpha_K b_K : ℝ) (R K : FieldR) (t x : ℝ) :
    dK alpha_K b_K R K t x
      =
      - alpha_K * (K t x)
    + b_K * (D1 R t x) := by
  rfl

-- Locked “CRFT reduction consistency” (structural shape):
-- When rotor/curvature are constrained to zero AND couplings are disabled,
-- the rho/u subsystem is:
--   ∂t ρ = −∂x(ρ u)
--   ∂t u = −u ∂x u − g_eff ∂x ρ + nu_eff ∂xx u
theorem reduction_rho_u
    (g_eff nu_eff : ℝ)
    (rho u R K : FieldR) :
    (du g_eff nu_eff 0 0 rho u R K)
      =
    (fun t x =>
        - (u t x) * (D1 u t x)
      - g_eff * (D1 rho t x)
      + nu_eff * (D2 u t x)) := by
  funext t x
  simp [du]

-- Locked “rotor isolation behavior” (structural):
-- With couplings disabled (b_R = 0, d_R = 0), rotor obeys ∂t R = −alpha_R R.
theorem rotor_isolation
    (alpha_R : ℝ) (u K R : FieldR) (t x : ℝ) :
    dR alpha_R 0 0 u K R t x = -alpha_R * (R t x) := by
  simp [dR, absR]

end

end V3
end LCRD
end ToeFormal
