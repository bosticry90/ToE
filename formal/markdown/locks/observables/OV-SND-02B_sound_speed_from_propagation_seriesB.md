# OV-SND-02B — Derived sound speed from propagation (seriesB) (computed)

Scope / limits
- Derived from frozen OV-SND-01N2 seriesB points only
- Pinned slope rule; no free creativity; no density inference
- Non-decisive by design

Record (computed)

```json
{
  "date": "2026-01-24",
  "fingerprint": "20847369ccb9572fda4fac8101ed61937ad10ca9e245567fa9c27344aea04810",
  "input_dataset": {
    "csv_relpath": "formal/external_evidence/bec_sound_andrews_1997/ovsnd01_digitization/distance_vs_time_squares_seriesB.csv",
    "csv_sha256": "9b8f88b829d5c3bcf1afbac48fc5a4c97c7327ab7cc6da3449ea0dd94d1127a6",
    "locked_record_fingerprint": "f240dd5a72a73606ba3eceff50dd0b1e278143e5c960dc50d8c51082ff249fa5",
    "locked_record_schema": "OV-SND-01N2_sound_propagation_distance_time_digitized/v2",
    "row_count": 9,
    "source_digitization_id": "OV-SND-01N2",
    "source_observable_id": "OV-SND-01N2",
    "source_series": "seriesB"
  },
  "method": {
    "primary": {
      "model": "distance_um = c_um_per_ms * time_ms",
      "name": "ols_through_origin",
      "rationale": "Pinned conservative estimator; avoids free intercept choice; physical expectation distance\u21920 at t\u21920."
    },
    "uncertainty": {
      "assumptions": [
        "homoscedastic_residuals",
        "independent_points"
      ],
      "type": "slope_standard_error"
    }
  },
  "observable_id": "OV-SND-02B",
  "results": {
    "density_dependence": {
      "note": "This record does not infer density n; mapping to density conditions is governed separately (OV-BR-SND-02).",
      "status": "not_inferred"
    },
    "primary": {
      "c_m_per_s": 0.001538351603139604,
      "c_um_per_ms": 1.538351603139604,
      "dof": 8,
      "n": 9,
      "residual_rms_um": 29.343612044045777,
      "se_m_per_s": 0.0001698139946589455,
      "se_um_per_ms": 0.1698139946589455
    }
  },
  "schema": "OV-SND-02B_sound_speed_from_propagation_seriesB/v1",
  "scope_limits": [
    "derived_from_frozen_points_only",
    "no_manual_clicking",
    "pinned_slope_rule",
    "no_density_inference",
    "non_decisive_by_design"
  ],
  "status": {
    "blocked": false,
    "blockers": []
  },
  "units": {
    "c": "m_per_s",
    "c_raw": "um_per_ms",
    "distance": "um",
    "time": "ms"
  }
}
```

Record fingerprint: `20847369ccb9572fda4fac8101ed61937ad10ca9e245567fa9c27344aea04810`
