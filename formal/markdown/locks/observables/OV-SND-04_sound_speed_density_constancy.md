# OV-SND-04 — Sound speed density constancy check (computed)

Scope / limits
- Bookkeeping / derived observable only; no physics validation claim
- Reports spread metrics only; no fitting; no universality/continuity claims

Record (computed)

```json
{
  "condition_rows": [
    {
      "K2_si_m5_per_s2": 2.0445715868274337e-26,
      "K_si_m32_per_s": 1.4298851656085652e-13,
      "c_m_per_s": 0.0014298851656085652,
      "condition_id": "snd02_single__central",
      "density_condition_key": "central",
      "n0_cm3": 100000000000000.0,
      "n0_m3": 1e+20,
      "pair_type": "same_source",
      "propagation_condition_key": "snd02_single",
      "rationale": "Declared pairing for OV-SND-04 constancy bookkeeping; not a claim of same experimental run beyond pinned Andrews source context.",
      "se_c_m_per_s": 0.0002711314608466893,
      "source_locators": {
        "density": {
          "density_condition_note": "Declared as the Andrews central density anchor condition_id=central.",
          "density_csv_relpath": "formal/external_evidence/bec_sound_andrews_1997/ovsnd03_density_digitization/central_density.csv",
          "density_lock_path": "formal/markdown/locks/observables/OV-SND-03_central_density_digitized.md"
        },
        "propagation": {
          "digitized_points_lock_path": "formal/markdown/locks/observables/OV-SND-01_sound_propagation_distance_time_digitized.md",
          "propagation_condition_note": "Declared as the default/single OV-SND-02 condition (Andrews Fig.2 squares seriesA).",
          "speed_lock_path": "formal/markdown/locks/observables/OV-SND-02_sound_speed_from_propagation.md"
        }
      }
    },
    {
      "K2_si_m5_per_s2": 4.187674448216826e-27,
      "K_si_m32_per_s": 6.471224341820353e-14,
      "c_m_per_s": 0.001538351603139604,
      "condition_id": "snd02b_seriesB__sk98_mu_digitized_01",
      "density_condition_key": "sk98_mu_digitized_01",
      "n0_cm3": 565116912536000.0,
      "n0_m3": 5.65116912536e+20,
      "pair_type": "cross_source_hypothesis",
      "propagation_condition_key": "snd02b_seriesB",
      "rationale": "Declared cross-source pairing hypothesis for OV-SND-04; conditional-on-mapping only; no implied condition identity unless separately evidenced.",
      "se_c_m_per_s": 0.0001698139946589455,
      "source_locators": {
        "density": {
          "density_condition_note": "Cross-source pairing hypothesis using OV-SND-03N2 rows_preview density_condition_key=sk98_mu_digitized_01.",
          "density_csv_relpath": "formal/external_evidence/bec_sound_density_secondary_TBD/ovsnd03n2_density_digitization/density_conditions.csv",
          "density_lock_path": "formal/markdown/locks/observables/OV-SND-03N2_secondary_density_conditions_digitized.md"
        },
        "propagation": {
          "digitized_points_lock_path": "formal/markdown/locks/observables/OV-SND-01N2_sound_propagation_distance_time_digitized.md",
          "propagation_condition_note": "Declared as OV-SND-02B derived from OV-SND-01N2 seriesB (largest-x-gap split).",
          "speed_lock_path": "formal/markdown/locks/observables/OV-SND-02B_sound_speed_from_propagation_seriesB.md"
        }
      }
    }
  ],
  "date": "2026-01-24",
  "fingerprint": "c7a0c4f14e3a3bb32f58f41ab0d277fc0c7f81e7f781d5cb1e35e21338c0f95f",
  "inputs": {
    "OV-BR-SND-02": {
      "lock_path": "formal/markdown/locks/observables/OV-BR-SND-02_cross_source_density_mapping.md",
      "record_fingerprint": "365869bd6a3ea7b9a0f4afc43aaa234bae28bd289f55866f42b811ddf55c26e4",
      "record_schema": "OV-BR-SND-02_cross_source_density_mapping/v1"
    },
    "OV-SND-02": {
      "lock_path": "formal/markdown/locks/observables/OV-SND-02_sound_speed_from_propagation.md",
      "record_fingerprint": "1e1e1f09907117e081fb9be9cab34d39884cf66acc8e2811d807e0a2db7a1dbe",
      "record_schema": "OV-SND-02_sound_speed_from_propagation/v1"
    },
    "OV-SND-02B": {
      "blocked": false,
      "blockers": [],
      "lock_path": "formal/markdown/locks/observables/OV-SND-02B_sound_speed_from_propagation_seriesB.md",
      "record_fingerprint": "20847369ccb9572fda4fac8101ed61937ad10ca9e245567fa9c27344aea04810",
      "record_schema": "OV-SND-02B_sound_speed_from_propagation_seriesB/v1"
    },
    "OV-SND-03N": {
      "lock_path": "formal/markdown/locks/observables/OV-SND-03_central_density_digitized.md",
      "record_fingerprint": "d5222e1b706c3c8455e3c0e04f23e14473a04ab2dcff64ba13f266270f8eae7a",
      "record_schema": "OV-SND-03_central_density_digitized/v1"
    },
    "OV-SND-03N2": {
      "blocked": false,
      "blockers": [],
      "lock_path": "formal/markdown/locks/observables/OV-SND-03N2_secondary_density_conditions_digitized.md",
      "record_fingerprint": "1b79934c23c803991487f9be9989ba880d3ee412779bd4049d07d66a4edd7dd5",
      "record_schema": "OV-SND-03N2_secondary_density_conditions_digitized/v1",
      "row_count": 2
    }
  },
  "observable_id": "OV-SND-04",
  "schema": "OV-SND-04_sound_speed_density_constancy/v2",
  "scope_limits": [
    "derived_bookkeeping_only",
    "no_universality_claim",
    "no_density_dependence_inference_beyond_spread_metrics",
    "no_continuity_claim",
    "no_cross_regime_averaging",
    "non_decisive_by_design"
  ],
  "status": {
    "blocked": false,
    "blockers": [],
    "n_pairs": 2,
    "reason": null,
    "required_min_pairs": 2
  },
  "summary": {
    "assumptions": [
      "no_density_uncertainty_modeled (density treated as fixed per digitization)",
      "speed_uncertainty_propagation_not_modeled_in_spread_metrics"
    ],
    "metrics": {
      "K": {
        "cv": 0.5329752625918229,
        "max_fractional_deviation_from_mean": 0.3768704223833588,
        "mean": 1.0385037998953003e-13
      },
      "K2": {
        "cv": 0.9333811699673482,
        "max_fractional_deviation_from_mean": 0.6600001547157455,
        "mean": 1.2316695158245582e-26
      },
      "n_pairs": 2
    }
  }
}
```

Record fingerprint: `c7a0c4f14e3a3bb32f58f41ab0d277fc0c7f81e7f781d5cb1e35e21338c0f95f`
