# OV-SND-03 — Sound speed density scaling (computed)

Scope / limits
- Bookkeeping / derived observable only; no physics validation claim
- Single-condition only; no density-dependence inference

Record (computed)

```json
{
  "date": "2026-01-24",
  "definitions": {
    "n0": {
      "conversion": "n0_m3 = n0_cm3 * 1e6 (since 1 cm^-3 = 1e6 m^-3)",
      "n0_cm3": 100000000000000.0,
      "n0_m3": 1e+20
    },
    "note": "Single-condition only; does not test constancy across multiple densities.",
    "scaled_quantities": [
      {
        "name": "K = c/sqrt(n0)",
        "units_cm": "m*cm^(3/2)/s",
        "units_si": "m^(3/2)/s"
      },
      {
        "name": "K2 = c^2/n0",
        "units_cm": "m^2*cm^3/s^2",
        "units_si": "m^5/s^2"
      }
    ]
  },
  "fingerprint": "37803d75828ce358ef3afaf040bf2d3d44385db797294b8b6c9e94762ce4211a",
  "inputs": {
    "OV-SND-02": {
      "c_m_per_s": 0.0014298851656085652,
      "lock_path": "formal/markdown/locks/observables/OV-SND-02_sound_speed_from_propagation.md",
      "locked_record_fingerprint": "1e1e1f09907117e081fb9be9cab34d39884cf66acc8e2811d807e0a2db7a1dbe",
      "locked_record_schema": "OV-SND-02_sound_speed_from_propagation/v1",
      "se_m_per_s": 0.0002711314608466893
    },
    "OV-SND-03N": {
      "lock_path": "formal/markdown/locks/observables/OV-SND-03_central_density_digitized.md",
      "locked_record_fingerprint": "d5222e1b706c3c8455e3c0e04f23e14473a04ab2dcff64ba13f266270f8eae7a",
      "locked_record_schema": "OV-SND-03_central_density_digitized/v1",
      "n0_cm3": 100000000000000.0
    }
  },
  "observable_id": "OV-SND-03",
  "results": {
    "K": {
      "value_cm_m_cm32_per_s": 1.4298851656085651e-10,
      "value_si_m32_per_s": 1.4298851656085652e-13
    },
    "K2": {
      "value_cm_m2_cm3_per_s2": 2.0445715868274337e-20,
      "value_si_m5_per_s2": 2.0445715868274337e-26
    },
    "n0": {
      "n0_cm3": 100000000000000.0,
      "n0_m3": 1e+20
    }
  },
  "schema": "OV-SND-03_sound_speed_density_scaling/v1",
  "scope_limits": [
    "derived_bookkeeping_only",
    "single_condition_only",
    "no_density_dependence_inference",
    "no_continuity_claim",
    "no_cross_regime_averaging",
    "non_decisive_by_design"
  ]
}
```

Record fingerprint: `37803d75828ce358ef3afaf040bf2d3d44385db797294b8b6c9e94762ce4211a`
