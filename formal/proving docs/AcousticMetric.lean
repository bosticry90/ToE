import Mathlib

namespace ToeFormal
namespace CRFT
namespace Geom

noncomputable section
set_option autoImplicit false

-- LOCK_GEOM_C10_C11_ACOUSTIC_METRIC.md
-- Primary implementation: acoustic_metric.py
-- Tests/diagnostics: crft/tests/crft_c7_acoustic_metric_diagnostics.py, crft/tests/crft_geom_c10_c11.py
--
-- Locked construction (pointwise):
--   c_s2 = g_eff * rho
--
-- 1D acoustic metric components (t,x):
--   g_tt = −(c_s2 − u^2)
--   g_tx = −u
--   g_xx = 1
-- det(g) = g_tt * g_xx − (g_tx)^2
--
-- 2D acoustic metric components (t,x,y):
--   g_tt = −(c_s2 − u_x^2 − u_y^2)
--   g_tx = −u_x
--   g_ty = −u_y
--   g_xx = 1
--   g_yy = 1
-- det(g) = g_tt*g_xx*g_yy − (g_tx)^2*g_yy − (g_ty)^2*g_xx
-- For g_xx=g_yy=1: det(g) = g_tt − (g_tx)^2 − (g_ty)^2
--
-- This file is a structural mirror: it locks formulas, not physical completeness.

-- Scalar fields (no time variable needed in the lock; computed pointwise on grids).
abbrev Scalar1D : Type := ℝ → ℝ
abbrev Scalar2D : Type := ℝ → ℝ → ℝ

/-- Local sound-speed-squared field: c_s2 = g_eff * rho. -/
def cs2_1d (rho : Scalar1D) (g_eff : ℝ) : Scalar1D :=
  fun x => g_eff * rho x

/-- Local sound-speed-squared field: c_s2 = g_eff * rho. -/
def cs2_2d (rho : Scalar2D) (g_eff : ℝ) : Scalar2D :=
  fun x y => g_eff * rho x y

/-- 1D acoustic metric as stored component fields (g_tt, g_tx, g_xx). -/
structure AcousticMetric1D where
  g_tt : Scalar1D
  g_tx : Scalar1D
  g_xx : Scalar1D

/-- 2D acoustic metric as stored component fields (g_tt, g_tx, g_ty, g_xx, g_yy).
Spatial cross terms (e.g. g_xy) are assumed zero and not represented. -/
structure AcousticMetric2D where
  g_tt : Scalar2D
  g_tx : Scalar2D
  g_ty : Scalar2D
  g_xx : Scalar2D
  g_yy : Scalar2D

/-- Authoritative 1D acoustic metric component construction. -/
def compute_acoustic_metric_1d (rho u : Scalar1D) (g_eff : ℝ) : AcousticMetric1D :=
  let cs2 : Scalar1D := cs2_1d rho g_eff
  { g_tt := fun x => - (cs2 x - (u x) ^ 2)
    g_tx := fun x => - (u x)
    g_xx := fun _ => (1 : ℝ) }

/-- Authoritative 1D determinant form: det(g) = g_tt*g_xx − (g_tx)^2. -/
def metric_determinant_1d (m : AcousticMetric1D) : Scalar1D :=
  fun x => (m.g_tt x) * (m.g_xx x) - (m.g_tx x) ^ 2

/-- Expansion lemma: 1D g_tt is definitionally the locked expression. -/
theorem acoustic_metric_1d_gtt_expand (rho u : Scalar1D) (g_eff : ℝ) (x : ℝ) :
    (compute_acoustic_metric_1d rho u g_eff).g_tt x
      = - ((cs2_1d rho g_eff) x - (u x) ^ 2) := by
  rfl

/-- Expansion lemma: 1D determinant is definitionally the locked expression. -/
theorem metric_det_1d_expand (m : AcousticMetric1D) (x : ℝ) :
    metric_determinant_1d m x = (m.g_tt x) * (m.g_xx x) - (m.g_tx x) ^ 2 := by
  rfl

/-- Authoritative 2D acoustic metric component construction. -/
def compute_acoustic_metric_2d (rho u_x u_y : Scalar2D) (g_eff : ℝ) : AcousticMetric2D :=
  let cs2 : Scalar2D := cs2_2d rho g_eff
  { g_tt := fun x y => - (cs2 x y - (u_x x y) ^ 2 - (u_y x y) ^ 2)
    g_tx := fun x y => - (u_x x y)
    g_ty := fun x y => - (u_y x y)
    g_xx := fun _ _ => (1 : ℝ)
    g_yy := fun _ _ => (1 : ℝ) }

/-- Authoritative 2D determinant form under vanishing spatial cross-terms:
det(g) = g_tt*g_xx*g_yy − (g_tx)^2*g_yy − (g_ty)^2*g_xx. -/
def metric_determinant_2d (m : AcousticMetric2D) : Scalar2D :=
  fun x y =>
    (m.g_tt x y) * (m.g_xx x y) * (m.g_yy x y)
    - (m.g_tx x y) ^ 2 * (m.g_yy x y)
    - (m.g_ty x y) ^ 2 * (m.g_xx x y)

/-- Expansion lemma: 2D determinant is definitionally the locked expression. -/
theorem metric_det_2d_expand (m : AcousticMetric2D) (x y : ℝ) :
    metric_determinant_2d m x y
      =
      (m.g_tt x y) * (m.g_xx x y) * (m.g_yy x y)
    - (m.g_tx x y) ^ 2 * (m.g_yy x y)
    - (m.g_ty x y) ^ 2 * (m.g_xx x y) := by
  rfl

/-- For metrics produced by `compute_acoustic_metric_2d`, g_xx = 1 and g_yy = 1,
so det(g) reduces to: det(g) = g_tt − (g_tx)^2 − (g_ty)^2. -/
theorem metric_det_2d_reduces_for_computed
    (rho u_x u_y : Scalar2D) (g_eff : ℝ) (x y : ℝ) :
    metric_determinant_2d (compute_acoustic_metric_2d rho u_x u_y g_eff) x y
      =
      (compute_acoustic_metric_2d rho u_x u_y g_eff).g_tt x y
      - ((compute_acoustic_metric_2d rho u_x u_y g_eff).g_tx x y) ^ 2
      - ((compute_acoustic_metric_2d rho u_x u_y g_eff).g_ty x y) ^ 2 := by
  simp [metric_determinant_2d, compute_acoustic_metric_2d]

end

end Geom
end CRFT
end ToeFormal
