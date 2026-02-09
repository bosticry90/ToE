import Mathlib

namespace ToeFormal
namespace CRFT

noncomputable section
set_option autoImplicit false

-- LOCK_PHI_CHI_1D_EXTENDED_CRFT.md
-- Canonical test:
--   crft.tests.crft_c5_multifield_consistency
--
-- Locked coupled φ–χ system (1D periodic; spectral derivatives in numerics):
--
-- Governing (authoritative) form:
--   i ∂t φ = -(1/2) ∂xx φ + g_eff (|φ|^2 - rho0) φ + alpha χ φ
--   ∂t χ = π
--   ∂t π = -(1/2) ∂xx χ - lambda_chi ∂xxxx χ - beta_chi ∂xxxxxx χ - gamma (|φ|^2 - rho0)
--
-- Implemented solved-for form (algebraically equivalent):
--   φ_t = i [ (1/2) ∂xx φ - g_eff (|φ|^2 - rho0) φ - alpha χ φ ]
--   χ_t = π
--   π_t = -(1/2) ∂xx χ - lambda_chi ∂xxxx χ - beta_chi ∂xxxxxx χ - gamma (|φ|^2 - rho0)
--
-- Locked reduction:
--   if alpha = 0, gamma = 0, and χ = 0, π = 0 identically,
--   then φ evolution reduces exactly to single-field CRFT first-order φ equation
--   and χ,π remain zero.

-- Fields (t, x).
abbrev FieldC : Type := ℝ → ℝ → ℂ
abbrev FieldR : Type := ℝ → ℝ → ℝ

-- Abstract spatial derivative operators (structural placeholders).
opaque DxxC : FieldC → FieldC
opaque DxxR : FieldR → FieldR
opaque DxxxxR : FieldR → FieldR
opaque DxxxxxxR : FieldR → FieldR

-- Minimal structural axioms needed to express the lock’s “exact reduction”
-- when χ ≡ 0 (since the derivatives are opaque in this layer).
axiom DxxR_zero : DxxR (fun _ _ => (0 : ℝ)) = (fun _ _ => (0 : ℝ))
axiom DxxxxR_zero : DxxxxR (fun _ _ => (0 : ℝ)) = (fun _ _ => (0 : ℝ))
axiom DxxxxxxR_zero : DxxxxxxR (fun _ _ => (0 : ℝ)) = (fun _ _ => (0 : ℝ))

-- Pointwise squared magnitude |φ|^2.
def absSq (phi : FieldC) : FieldR :=
  fun t x => Complex.normSq (phi t x)

-- Real-field subtraction (|φ|^2 - rho0).
def rhoDelta (rho0 : ℝ) (phi : FieldC) : FieldR :=
  fun t x => absSq phi t x - rho0

-- Multiply a real-valued coefficient field into a complex field (pointwise).
def smulRC (a : FieldR) (phi : FieldC) : FieldC :=
  fun t x => (a t x : ℂ) * (phi t x)

-- φ_t = i [ (1/2) φ_xx - g_eff (|φ|^2 - rho0) φ - alpha χ φ ]
def dphi_coupled (g_eff rho0 alpha : ℝ) (phi : FieldC) (chi : FieldR) : FieldC :=
  fun t x =>
    Complex.I
      * ( ((1 : ℂ) / (2 : ℂ)) * (DxxC phi t x)
        - (g_eff : ℂ) * (smulRC (rhoDelta rho0 phi) phi t x)
        - (alpha : ℂ) * ((chi t x : ℂ) * (phi t x)) )

-- χ_t = π
def dchi_coupled (pi : FieldR) : FieldR :=
  fun t x => pi t x

-- π_t = -(1/2) χ_xx - lambda_chi χ_xxxx - beta_chi χ_xxxxxx - gamma (|φ|^2 - rho0)
def dpi_coupled (rho0 lambda_chi beta_chi gamma : ℝ) (phi : FieldC) (chi pi : FieldR) : FieldR :=
  let _ := pi
  fun t x =>
      - (1 / 2 : ℝ) * (DxxR chi t x)
    - lambda_chi * (DxxxxR chi t x)
    - beta_chi   * (DxxxxxxR chi t x)
    - gamma * (rhoDelta rho0 phi t x)

-- Single-field CRFT first-order φ RHS (reduction target):
--   i ∂t φ = -(1/2) ∂xx φ + g_eff (|φ|^2 - rho0) φ
-- ⇒ φ_t = i [ (1/2) ∂xx φ - g_eff (|φ|^2 - rho0) φ ]
def dphi_single (g_eff rho0 : ℝ) (phi : FieldC) : FieldC :=
  fun t x =>
    Complex.I
      * ( ((1 : ℂ) / (2 : ℂ)) * (DxxC phi t x)
        - (g_eff : ℂ) * (smulRC (rhoDelta rho0 phi) phi t x) )

-- Reduction theorem (exact, structural; matches the lock’s equality intent).
theorem reduction_property
    (g_eff rho0 alpha gamma lambda_chi beta_chi : ℝ)
    (phi : FieldC) (chi pi : FieldR)
    (hAlpha : alpha = 0)
    (hGamma : gamma = 0)
    (hChi   : ∀ t x : ℝ, chi t x = 0)
    (hPi    : ∀ t x : ℝ, pi t x = 0) :
    (dphi_coupled g_eff rho0 alpha phi chi = dphi_single g_eff rho0 phi)
    ∧ (dchi_coupled pi = (fun t x => 0))
    ∧ (dpi_coupled rho0 lambda_chi beta_chi gamma phi chi pi = (fun t x => 0)) := by
  -- Promote pointwise equalities to function equalities so we can rewrite under opaque operators.
  have hChiFun : chi = (fun _ _ => (0 : ℝ)) := by
    funext t x
    exact hChi t x
  have hPiFun : pi = (fun _ _ => (0 : ℝ)) := by
    funext t x
    exact hPi t x

  constructor
  · -- dphi_coupled = dphi_single
    funext t x
    simp [dphi_coupled, dphi_single, hAlpha, hChi, rhoDelta, absSq]
  · constructor
    · -- dchi_coupled pi = 0
      funext t x
      simp [dchi_coupled, hPi]
    · -- dpi_coupled = 0 (gamma = 0, chi = 0 ⇒ derivative terms vanish structurally)
      funext t x
      -- rewrite chi and pi to the zero functions to use the zero axioms
      subst hChiFun
      subst hPiFun
      -- now the derivative terms are definitionally on (fun _ _ => 0)
      simp [dpi_coupled, hGamma, rhoDelta, absSq, DxxR_zero, DxxxxR_zero, DxxxxxxR_zero]

end
end CRFT
end ToeFormal
