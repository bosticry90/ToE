# OV-SND-02 — Derived sound speed from propagation (computed)

Scope / limits
- Derived from frozen OV-SND-01N points only
- Pinned slope rule; no free creativity; no density inference
- No continuity/averaging across regimes; non-decisive by design

Record (computed)

```json
{
  "date": "2026-01-24",
  "fingerprint": "1e1e1f09907117e081fb9be9cab34d39884cf66acc8e2811d807e0a2db7a1dbe",
  "input_dataset": {
    "csv_relpath": "formal/external_evidence/bec_sound_andrews_1997/ovsnd01_digitization/distance_vs_time_squares.csv",
    "csv_sha256": "2b1b2c77b106e474ffd80b48e977fb6ff6b988036e2e75fdabc82e93a8391021",
    "locked_record_fingerprint": "adfb63b0dbd71622df7670196f3646e0ec053eacd271b66079762a9122ce3530",
    "locked_record_schema": "OV-SND-01_sound_propagation_distance_time_digitized/v1",
    "row_count": 11,
    "source_digitization_id": "OV-SND-01N",
    "source_observable_id": "OV-SND-01"
  },
  "method": {
    "diagnostic": {
      "model": "distance_um = a_um + c_um_per_ms * time_ms",
      "name": "ols_with_intercept",
      "used_for": "sanity_check_only"
    },
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
  "observable_id": "OV-SND-02",
  "results": {
    "density_dependence": {
      "note": "This record does not infer density n; symbolic scaling is recorded separately in OV-SND-01.",
      "status": "not_inferred"
    },
    "diagnostic": {
      "a_um": 45.67702556059195,
      "c_um_per_ms": 0.4822560184584133,
      "dof": 9,
      "n": 11,
      "residual_rms_um": 29.241992904921144,
      "se_a_um": 20.559537962363695,
      "se_um_per_ms": 0.48443954185554133
    },
    "primary": {
      "c_m_per_s": 0.0014298851656085652,
      "c_um_per_ms": 1.4298851656085652,
      "dof": 10,
      "n": 11,
      "residual_rms_um": 36.38762243736003,
      "se_m_per_s": 0.0002711314608466893,
      "se_um_per_ms": 0.27113146084668927
    }
  },
  "schema": "OV-SND-02_sound_speed_from_propagation/v1",
  "scope_limits": [
    "derived_from_frozen_points_only",
    "no_fitting_beyond_pinned_slope_rule",
    "no_density_inference",
    "no_parameter_inference_beyond_c",
    "no_continuity_claim",
    "no_cross_regime_averaging",
    "non_decisive_by_design"
  ],
  "units": {
    "c": "m_per_s",
    "c_raw": "um_per_ms",
    "distance": "um",
    "time": "ms"
  }
}
```

Record fingerprint: `1e1e1f09907117e081fb9be9cab34d39884cf66acc8e2811d807e0a2db7a1dbe`
