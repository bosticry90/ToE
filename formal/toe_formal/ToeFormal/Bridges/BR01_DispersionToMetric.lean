import Mathlib
import ToeFormal.CRFT.Geom.AcousticMetric

namespace ToeFormal
namespace Bridges
namespace BR01

open ToeFormal.CRFT.Geom

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Minimal 1D DR-01 surrogate for the BR-01 bridge.

Interpreted as the effective dispersion form:
  ω(k) = u*k + c_s*|k|

At this structural layer, BR-01 only records a mapping from such a DR object to
an MT-01 acoustic metric object.
-/
structure DR01Fit1D where
  u : ℝ
  c_s : ℝ

/-- Minimal DR-01 fit artifact type for BR-01 consumers.

This is intentionally definitionally compatible with `DR01Fit1D` (same fields),
but lets downstream Lean code depend on a “fit-typed” assumption rather than a
free-form surrogate.
-/
structure DR01FitArtifact1D where
  u : ℝ
  c_s : ℝ

def DR01FitArtifact1D.toSurrogate (fit : DR01FitArtifact1D) : DR01Fit1D :=
  { u := fit.u, c_s := fit.c_s }

/-- BR-01 mapping in the canonical “unit density” gauge:
- choose rho ≡ 1
- choose g_eff = c_s^2
- choose the CRFT velocity field u(x) ≡ u

Then the MT-01 construction satisfies c_s^2 = g_eff * rho definitionally.
-/
def metricFromDR01_unitDensity (dr : DR01Fit1D) : AcousticMetric1D :=
  compute_acoustic_metric_1d (rho := fun _ => (1 : ℝ)) (u := fun _ => dr.u) (g_eff := dr.c_s ^ 2)

/-- Wrapper: BR-01 mapping that consumes a DR-01 fit artifact. -/
def metricFromDR01Fit_unitDensity (fit : DR01FitArtifact1D) : AcousticMetric1D :=
  metricFromDR01_unitDensity (DR01FitArtifact1D.toSurrogate fit)

end

end BR01
end Bridges
end ToeFormal
