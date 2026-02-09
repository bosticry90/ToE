# OV-BR-04A — Bragg low-k slope (condition_A) (computed)

Scope / limits
- Derived from frozen OV-BR-03N points only
- Deterministic low-k window + pinned slope rule
- Bookkeeping / anchoring only; no ToE validation claim

Record (computed)

```json
{
  "condition_key": "condition_A",
  "condition_semantic": "filled circles",
  "date": "2026-01-25",
  "fingerprint": "e6c54b4ec1a93be70542faa6d1650365fb91f810c39ea56e73ed95f0e7f377c1",
  "input_dataset": {
    "condition_key": "condition_A",
    "condition_semantic": "filled circles",
    "csv_relpath": "formal/external_evidence/bec_bragg_shammass_2012/ovbr03n_digitization/k_omega_conditionA.csv",
    "csv_sha256": "07c2f78e20db8afc81b3f57f494947b027e13ed78c32f1a639cd8f9b3c7613d7",
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
  "observable_id": "OV-BR-04A",
  "results": {
    "diagnostic": {
      "a_kHz": 0.5002998447566884,
      "dof": 3,
      "n": 5,
      "r2": 0.3468337663215413,
      "residual_rms_kHz": 0.27926004059505455,
      "s_kHz_per_um_inv": 0.6498074713077385,
      "se_a_kHz": 0.29688715512047714,
      "se_kHz_per_um_inv": 0.5148435185105142
    },
    "primary": {
      "c_mm_per_s": 1.3783106701297123,
      "dof": 4,
      "n": 5,
      "residual_rms_kHz": 0.3896231606578541,
      "s_kHz_per_um_inv": 1.3783106701297123,
      "se_kHz_per_um_inv": 0.3378303093727233,
      "se_mm_per_s": 0.3378303093727233
    }
  },
  "schema": "OV-BR-04A_bragg_lowk_slope_conditionA/v2",
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
        "k_um_inv": 0.0111058280125,
        "omega_over_2pi_kHz": 0.281223501438
      },
      {
        "k_um_inv": 0.278366050808,
        "omega_over_2pi_kHz": 1.04467231387
      },
      {
        "k_um_inv": 0.551172055427,
        "omega_over_2pi_kHz": 0.567632634864
      },
      {
        "k_um_inv": 0.6628926097,
        "omega_over_2pi_kHz": 1.24262148908
      },
      {
        "k_um_inv": 0.917511547344,
        "omega_over_2pi_kHz": 0.938564422648
      }
    ],
    "rule_id": "lowk_window_v1",
    "selected_row_count": 5
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

Record fingerprint: `e6c54b4ec1a93be70542faa6d1650365fb91f810c39ea56e73ed95f0e7f377c1`
