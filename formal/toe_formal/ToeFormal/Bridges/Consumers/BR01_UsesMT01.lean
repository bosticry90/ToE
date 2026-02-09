import ToeFormal.Bridges.BR01_DispersionToMetric
import ToeFormal.CRFT.Geom.MT01_AcousticMetricConsumer

namespace ToeFormal
namespace Bridges
namespace Consumers

open ToeFormal.CRFT.Geom

noncomputable section
set_option autoImplicit false

/-- Example consumer: BR-01 → MT-01 composition.

This file intentionally consumes BR-01 only via its front-door mapping and then
routes the consequence through the MT-01 consumer lemma.
-/
theorem br01_metric_det_1d_reduces
    (dr : BR01.DR01Fit1D) (x : ℝ) :
    metric_determinant_1d (BR01.metricFromDR01_unitDensity dr) x
      =
      (BR01.metricFromDR01_unitDensity dr).g_tt x
      - ((BR01.metricFromDR01_unitDensity dr).g_tx x) ^ 2 := by
  simpa [BR01.metricFromDR01_unitDensity]
    using
      (metric_det_1d_reduces_for_computed
        (rho := fun _ => (1 : ℝ))
        (u := fun _ => dr.u)
        (g_eff := dr.c_s ^ 2)
        (x := x))

/-- Same consumer, but depending on a DR-01 fit artifact type. -/
theorem br01_metric_det_1d_reduces_from_fit
    (fit : BR01.DR01FitArtifact1D) (x : ℝ) :
    metric_determinant_1d (BR01.metricFromDR01Fit_unitDensity fit) x
      =
      (BR01.metricFromDR01Fit_unitDensity fit).g_tt x
      - ((BR01.metricFromDR01Fit_unitDensity fit).g_tx x) ^ 2 := by
  simpa [BR01.metricFromDR01Fit_unitDensity, BR01.metricFromDR01_unitDensity, BR01.DR01FitArtifact1D.toSurrogate]
    using
      (metric_det_1d_reduces_for_computed
        (rho := fun _ => (1 : ℝ))
        (u := fun _ => fit.u)
        (g_eff := fit.c_s ^ 2)
        (x := x))

end

end Consumers
end Bridges
end ToeFormal
