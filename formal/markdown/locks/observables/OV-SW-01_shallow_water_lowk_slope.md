# OV-SW-01 — Shallow-water low-k slope (computed)

Scope / limits
- Bookkeeping-only Axis C lane ingestion + slope extraction
- Pinned through-origin slope rule; no free intercept; no weighting
- No cross-lane pairing or comparability; non-decisive by design

Record (computed)

```json
{
  "date": "2026-01-25",
  "fingerprint": "84249163534dd44f37f770da3574488dd53371bc97b9c4f5c52f5aa555643e05",
  "input_dataset": null,
  "method": {
    "primary": {
      "model": "f_s_inv = slope_s_inv_per_m_inv * k_m_inv",
      "name": "ols_through_origin",
      "rationale": "Pinned through-origin slope rule; avoids free intercept choice; no cross-lane interpretation."
    },
    "uncertainty": {
      "assumptions": [
        "homoscedastic_residuals",
        "independent_points"
      ],
      "type": "slope_standard_error"
    }
  },
  "observable_id": "OV-SW-01",
  "results": null,
  "rows": [],
  "schema": "OV-SW-01_shallow_water_lowk_slope/v1",
  "scope_limits": [
    "bookkeeping_only",
    "no_cross_lane_pairing",
    "no_physics_claim",
    "no_fitting_beyond_pinned_slope_rule",
    "no_intercept",
    "no_weighting",
    "non_decisive_by_design"
  ],
  "status": {
    "blocked": true,
    "blockers": [
      "omega_over_2pi_vs_k_lowk_csv_missing",
      "omega_over_2pi_vs_k_lowk_metadata_missing"
    ]
  },
  "units": {
    "f": "s^-1",
    "k": "m^-1",
    "slope": "m_per_s",
    "slope_raw": "s^-1_per_m^-1"
  }
}
```

Record fingerprint: `84249163534dd44f37f770da3574488dd53371bc97b9c4f5c52f5aa555643e05`
