import ToeFormal.CRFT.Geom.AcousticMetric

namespace ToeFormal
namespace CRFT
namespace Geom

noncomputable section
set_option autoImplicit false

/-- For metrics produced by `compute_acoustic_metric_1d`, g_xx = 1, so
`det(g) = g_tt − (g_tx)^2`. -/
theorem metric_det_1d_reduces_for_computed
    (rho u : Scalar1D) (g_eff : ℝ) (x : ℝ) :
    metric_determinant_1d (compute_acoustic_metric_1d rho u g_eff) x
      =
      (compute_acoustic_metric_1d rho u g_eff).g_tt x
      - ((compute_acoustic_metric_1d rho u g_eff).g_tx x) ^ 2 := by
  simp [metric_determinant_1d, compute_acoustic_metric_1d]

end

end Geom
end CRFT
end ToeFormal
