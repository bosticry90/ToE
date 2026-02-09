# OV-BR-04B — Bragg low-k slope (condition_B) (computed)

Scope / limits
- Derived from frozen OV-BR-03N points only
- Deterministic low-k window + pinned slope rule
- Bookkeeping / anchoring only; no ToE validation claim

Record (computed)

```json
{
  "condition_key": "condition_B",
  "condition_semantic": "open circles",
  "date": "2026-01-25",
  "fingerprint": "f4b947cd26cd67c371d6e31c1dda1e0f4f19d8b542b35b39391742baf7b171b6",
  "input_dataset": {
    "condition_key": "condition_B",
    "condition_semantic": "open circles",
    "csv_relpath": "formal/external_evidence/bec_bragg_shammass_2012/ovbr03n_digitization/k_omega_conditionB.csv",
    "csv_sha256": "79c4877b7804170fa14ab5c50b7d9c5215158cf9ec3e6b2d655f0544a3a7e3e4",
    "locked_record_fingerprint": "42751965b20c1b6b2d5897bbfea088a04f0cc15cb74c5e1e27a4e3d0dc92701f",
    "locked_record_schema": "OV-BR-03N/v1",
    "row_count": 25,
    "source_digitization_id": "OV-BR-03N",
    "source_observable_id": "OV-BR-03N",
    "source_png_relpath": "formal/external_evidence/bec_bragg_shammass_2012/page_renders/page6_z4.png",
    "source_png_sha256": "54f38f343e3e3bb329fdaf539ed9e0ea2ed0dc87667b4afc981263f6845002ed"
  },
  "method": {
    "diagnostic": {
      "model": "omega_over_2pi_kHz = a_kHz + s_kHz_per_um_inv * k_um_inv",
      "name": "ols_with_intercept",
      "used_for": "sanity_check_only"
    },
    "primary": {
      "model": "omega_over_2pi_kHz = s_kHz_per_um_inv * k_um_inv",
      "name": "ols_through_origin",
      "rationale": "Pinned conservative estimator; avoids free intercept; physical expectation omega\u21920 as k\u21920."
    },
    "uncertainty": {
      "assumptions": [
        "homoscedastic_residuals",
        "independent_points"
      ],
      "type": "slope_standard_error"
    }
  },
  "observable_id": "OV-BR-04B",
  "results": {
    "diagnostic": {
      "a_kHz": 0.028116128062588515,
      "dof": 4,
      "n": 6,
      "r2": 0.5962500724155817,
      "residual_rms_kHz": 0.19948705048925205,
      "s_kHz_per_um_inv": 0.9284219111168761,
      "se_a_kHz": 0.21329149953704213,
      "se_kHz_per_um_inv": 0.38199474817111057
    },
    "primary": {
      "c_mm_per_s": 0.9729313348425234,
      "dof": 5,
      "n": 6,
      "residual_rms_kHz": 0.19991988089318824,
      "s_kHz_per_um_inv": 0.9729313348425234,
      "se_kHz_per_um_inv": 0.16012340869413266,
      "se_mm_per_s": 0.16012340869413266
    }
  },
  "schema": "OV-BR-04B_bragg_lowk_slope_conditionB/v2",
  "scope_limits": [
    "derived_from_frozen_points_only",
    "deterministic_selection_rule_only",
    "no_parameter_inference_beyond_slope",
    "no_cross_regime_averaging",
    "non_decisive_by_design"
  ],
  "selection": {
    "parameters": {
      "k_um_inv_max": 1.0,
      "omega_over_2pi_kHz_max": 1.3,
      "omega_over_2pi_kHz_min": 0.1
    },
    "rows_preview": [
      {
        "k_um_inv": 0.0532468414618,
        "omega_over_2pi_kHz": 0.275324539089
      },
      {
        "k_um_inv": 0.292276864556,
        "omega_over_2pi_kHz": 0.177241614434
      },
      {
        "k_um_inv": 0.52065510848,
        "omega_over_2pi_kHz": 0.471890639423
      },
      {
        "k_um_inv": 0.536503192501,
        "omega_over_2pi_kHz": 0.373407463743
      },
      {
        "k_um_inv": 0.712918387926,
        "omega_over_2pi_kHz": 0.471890639423
      },
      {
        "k_um_inv": 0.845683331069,
        "omega_over_2pi_kHz": 1.14826256851
      }
    ],
    "rule_id": "lowk_window_v1",
    "selected_row_count": 6
  },
  "status": {
    "admissibility_manifest": {
      "path": "formal/markdown locks/gates/admissibility_manifest_ENABLED_OVERRIDE.json",
      "version": 5
    },
    "blocked": false,
    "debug": {
      "manifest_input_path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\markdown locks\\gates\\admissibility_manifest_ENABLED_OVERRIDE.json",
      "manifest_resolved_path": "formal/markdown locks/gates/admissibility_manifest_ENABLED_OVERRIDE.json",
      "manifest_sha256": "2f9c1aa1dbcc30451ac0740cb09d85c1d12b6490efb02d449e453cc0de94c13f",
      "manifest_version": 5
    },
    "reasons": [],
    "required_gates": [
      "CT01",
      "SYM01",
      "CAUS01"
    ]
  },
  "units": {
    "k": "um_inv",
    "omega_over_2pi": "kHz",
    "slope": "kHz_per_um_inv",
    "velocity_candidate": "mm_per_s"
  }
}
```

Record fingerprint: `f4b947cd26cd67c371d6e31c1dda1e0f4f19d8b542b35b39391742baf7b171b6`
