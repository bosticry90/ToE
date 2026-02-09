# OV-BR-SND-03 — Cross-lane low-k consistency audit (computed)

Scope / limits
- Audit only; no physics claim
- Must remain valid even when no Bragg↔Sound mapping exists

Record (computed)

```json
{
  "bragg_date": "2026-01-25",
  "comparability": {
    "conversion_chain": {
      "bragg": {
        "assumptions": [
          "uses_unit_identities_pinned_in_OV-BR-04A/B",
          "no_additional_physical_equivalence_claim"
        ],
        "input": {
          "quantity": "low_k_slope_of_omega_over_2pi_vs_k",
          "slope_units": "(kHz)/(um^-1)",
          "x_units": "um^-1",
          "y_units": "kHz"
        },
        "to_m_per_s": {
          "factor": 0.001,
          "identity": "1 (mm/s) = 1e-3 (m/s)"
        },
        "velocity_candidate": {
          "exported_key": "c_mm_per_s",
          "identity": "1 (kHz)/(um^-1) = 1 (mm/s)",
          "quantity": "c",
          "units": "mm/s"
        }
      },
      "rule_id": "unit_chain_v1",
      "sound": {
        "assumptions": [
          "derived_from_frozen_distance_time_points_only"
        ],
        "input": {
          "exported_key": "c_m_per_s",
          "quantity": "sound_speed",
          "units": "m/s"
        }
      }
    },
    "criterion": {
      "criterion_id": "lowk_velocity_ratio_v1",
      "eps": 1e-12,
      "metric": "rel_err = abs(v_bragg_m_per_s - v_sound_m_per_s) / max(abs(v_sound_m_per_s), eps)",
      "prerequisites": [
        "unit_labels_pinned_in_upstream_records",
        "explicit_cross_lane_pairing_present"
      ],
      "rationale": "Pinned conservative tolerance for numeric comparability after explicit unit conversion; no systematic-error model.",
      "tolerance": 0.15
    },
    "reasons": [
      "CONVERSION_CHAIN_PINNED",
      "CRITERION_DEFINED",
      "WITHIN_TOL"
    ],
    "status": "established"
  },
  "fingerprint": "34e6c6c6c0a7598a316273eba3295999632e36bc36442a6993de89859884d2db",
  "notes": "This audit does not assert physical comparability. It reports locked derived outputs and explicitly pins a unit conversion chain + numeric criterion. Cross-lane comparison is only computed when an explicit Bragg\u2194Sound pairing exists.",
  "observable_id": "OV-BR-SND-03",
  "rows": [
    {
      "bragg_key": "br04a_conditionA",
      "comparability": {
        "notes": "Comparison is only computed when an explicit cross-lane pairing exists; otherwise prerequisites are reported only.",
        "reason_codes": [
          "CONVERSION_CHAIN_PINNED",
          "CRITERION_DEFINED",
          "WITHIN_TOL"
        ],
        "status": "pass"
      },
      "conversion_chain": {
        "bragg": {
          "assumptions": [
            "uses_unit_identities_pinned_in_OV-BR-04A/B",
            "no_additional_physical_equivalence_claim"
          ],
          "input": {
            "quantity": "low_k_slope_of_omega_over_2pi_vs_k",
            "slope_units": "(kHz)/(um^-1)",
            "x_units": "um^-1",
            "y_units": "kHz"
          },
          "to_m_per_s": {
            "factor": 0.001,
            "identity": "1 (mm/s) = 1e-3 (m/s)"
          },
          "velocity_candidate": {
            "exported_key": "c_mm_per_s",
            "identity": "1 (kHz)/(um^-1) = 1 (mm/s)",
            "quantity": "c",
            "units": "mm/s"
          }
        },
        "rule_id": "unit_chain_v1",
        "sound": {
          "assumptions": [
            "derived_from_frozen_distance_time_points_only"
          ],
          "input": {
            "exported_key": "c_m_per_s",
            "quantity": "sound_speed",
            "units": "m/s"
          }
        }
      },
      "criterion": {
        "criterion_id": "lowk_velocity_ratio_v1",
        "eps": 1e-12,
        "metric": "rel_err = abs(v_bragg_m_per_s - v_sound_m_per_s) / max(abs(v_sound_m_per_s), eps)",
        "prerequisites": [
          "unit_labels_pinned_in_upstream_records",
          "explicit_cross_lane_pairing_present"
        ],
        "rationale": "Pinned conservative tolerance for numeric comparability after explicit unit conversion; no systematic-error model.",
        "tolerance": 0.15
      },
      "derived": {
        "abs_diff_m_per_s": 5.15744954788528e-05,
        "bragg_velocity_candidate_m_per_s": 0.0013783106701297124,
        "bragg_velocity_candidate_se_m_per_s": 0.0003378303093727233,
        "pass": true,
        "rel_err": 0.036068977229302523,
        "sound_velocity_m_per_s": 0.0014298851656085652,
        "sound_velocity_se_m_per_s": 0.0002711314608466893,
        "z_score": 0.11906125047726067
      },
      "mapping_tuple_id": null,
      "pair_id": "br04a_conditionA__snd02_single",
      "pair_type": "cross_source_hypothesis",
      "sound_key": "snd02_single",
      "source_locators": {
        "bragg": {
          "fingerprint": "f0b46e7301ab42be108648ce8e550f7a7383fa4b1a4013f92059395a03a0cdf2",
          "lock_path": "formal/markdown/locks/observables/OV-BR-04A_bragg_lowk_slope_conditionA.md",
          "schema": "OV-BR-04A_bragg_lowk_slope_conditionA/v2",
          "source": {
            "figure": "Fig. 2",
            "page_render": "page6_z4.png",
            "pdf_relpath": "formal/external_evidence/bec_bragg_shammass_2012/source.pdf",
            "pdf_sha256": "ef5416e243b0863dada51b68483b72edf83e3b3870bf417b9215b236ea61207c",
            "png_relpath": "formal/external_evidence/bec_bragg_shammass_2012/page_renders/page6_z4.png",
            "png_sha256": "54f38f343e3e3bb329fdaf539ed9e0ea2ed0dc87667b4afc981263f6845002ed"
          }
        },
        "regime": {
          "fingerprint": "3bb051329ae22c1f9649cca702f26c4cbe4adf8adcbc84cf0d9e79f880e5e8ac",
          "lock_path": "formal/markdown/locks/observables/OV-BR-02_regime_bridge_record.md",
          "schema": "OV-BR-02/v1"
        },
        "sound": {
          "fingerprint": "1e1e1f09907117e081fb9be9cab34d39884cf66acc8e2811d807e0a2db7a1dbe",
          "lock_path": "formal/markdown/locks/observables/OV-SND-02_sound_speed_from_propagation.md",
          "schema": "OV-SND-02_sound_speed_from_propagation/v1"
        }
      },
      "values": {
        "bragg_se": 0.3378303093727233,
        "bragg_value": 1.3783106701297123,
        "bragg_velocity_candidate_units": "mm_per_s",
        "sound_c_units": "m_per_s",
        "sound_se": 0.0002711314608466893,
        "sound_value": 0.0014298851656085652
      }
    },
    {
      "bragg_key": "br04a_conditionA",
      "comparability": {
        "notes": "Comparison is only computed when an explicit cross-lane pairing exists; otherwise prerequisites are reported only.",
        "reason_codes": [
          "CONVERSION_CHAIN_PINNED",
          "CRITERION_DEFINED",
          "NO_MAPPING_TUPLE",
          "NO_JUSTIFIED_PAIRING"
        ],
        "status": "not_compared"
      },
      "conversion_chain": {
        "bragg": {
          "assumptions": [
            "uses_unit_identities_pinned_in_OV-BR-04A/B",
            "no_additional_physical_equivalence_claim"
          ],
          "input": {
            "quantity": "low_k_slope_of_omega_over_2pi_vs_k",
            "slope_units": "(kHz)/(um^-1)",
            "x_units": "um^-1",
            "y_units": "kHz"
          },
          "to_m_per_s": {
            "factor": 0.001,
            "identity": "1 (mm/s) = 1e-3 (m/s)"
          },
          "velocity_candidate": {
            "exported_key": "c_mm_per_s",
            "identity": "1 (kHz)/(um^-1) = 1 (mm/s)",
            "quantity": "c",
            "units": "mm/s"
          }
        },
        "rule_id": "unit_chain_v1",
        "sound": {
          "assumptions": [
            "derived_from_frozen_distance_time_points_only"
          ],
          "input": {
            "exported_key": "c_m_per_s",
            "quantity": "sound_speed",
            "units": "m/s"
          }
        }
      },
      "criterion": {
        "criterion_id": "lowk_velocity_ratio_v1",
        "eps": 1e-12,
        "metric": "rel_err = abs(v_bragg_m_per_s - v_sound_m_per_s) / max(abs(v_sound_m_per_s), eps)",
        "prerequisites": [
          "unit_labels_pinned_in_upstream_records",
          "explicit_cross_lane_pairing_present"
        ],
        "rationale": "Pinned conservative tolerance for numeric comparability after explicit unit conversion; no systematic-error model.",
        "tolerance": 0.15
      },
      "derived": {
        "abs_diff_m_per_s": null,
        "bragg_velocity_candidate_m_per_s": 0.0013783106701297124,
        "bragg_velocity_candidate_se_m_per_s": 0.0003378303093727233,
        "pass": null,
        "rel_err": null,
        "sound_velocity_m_per_s": 0.001538351603139604,
        "sound_velocity_se_m_per_s": 0.0001698139946589455,
        "z_score": null
      },
      "mapping_tuple_id": null,
      "pair_id": "br04a_conditionA__snd02b_seriesB",
      "pair_type": "none",
      "sound_key": "snd02b_seriesB",
      "source_locators": {
        "bragg": {
          "fingerprint": "f0b46e7301ab42be108648ce8e550f7a7383fa4b1a4013f92059395a03a0cdf2",
          "lock_path": "formal/markdown/locks/observables/OV-BR-04A_bragg_lowk_slope_conditionA.md",
          "schema": "OV-BR-04A_bragg_lowk_slope_conditionA/v2",
          "source": {
            "figure": "Fig. 2",
            "page_render": "page6_z4.png",
            "pdf_relpath": "formal/external_evidence/bec_bragg_shammass_2012/source.pdf",
            "pdf_sha256": "ef5416e243b0863dada51b68483b72edf83e3b3870bf417b9215b236ea61207c",
            "png_relpath": "formal/external_evidence/bec_bragg_shammass_2012/page_renders/page6_z4.png",
            "png_sha256": "54f38f343e3e3bb329fdaf539ed9e0ea2ed0dc87667b4afc981263f6845002ed"
          }
        },
        "regime": {
          "fingerprint": "3bb051329ae22c1f9649cca702f26c4cbe4adf8adcbc84cf0d9e79f880e5e8ac",
          "lock_path": "formal/markdown/locks/observables/OV-BR-02_regime_bridge_record.md",
          "schema": "OV-BR-02/v1"
        },
        "sound": {
          "fingerprint": "20847369ccb9572fda4fac8101ed61937ad10ca9e245567fa9c27344aea04810",
          "lock_path": "formal/markdown/locks/observables/OV-SND-02B_sound_speed_from_propagation_seriesB.md",
          "schema": "OV-SND-02B_sound_speed_from_propagation_seriesB/v1"
        }
      },
      "values": {
        "bragg_se": 0.3378303093727233,
        "bragg_value": 1.3783106701297123,
        "bragg_velocity_candidate_units": "mm_per_s",
        "sound_c_units": "m_per_s",
        "sound_se": 0.0001698139946589455,
        "sound_value": 0.001538351603139604
      }
    },
    {
      "bragg_key": "br04b_conditionB",
      "comparability": {
        "notes": "Comparison is only computed when an explicit cross-lane pairing exists; otherwise prerequisites are reported only.",
        "reason_codes": [
          "CONVERSION_CHAIN_PINNED",
          "CRITERION_DEFINED",
          "NO_MAPPING_TUPLE",
          "NO_JUSTIFIED_PAIRING"
        ],
        "status": "not_compared"
      },
      "conversion_chain": {
        "bragg": {
          "assumptions": [
            "uses_unit_identities_pinned_in_OV-BR-04A/B",
            "no_additional_physical_equivalence_claim"
          ],
          "input": {
            "quantity": "low_k_slope_of_omega_over_2pi_vs_k",
            "slope_units": "(kHz)/(um^-1)",
            "x_units": "um^-1",
            "y_units": "kHz"
          },
          "to_m_per_s": {
            "factor": 0.001,
            "identity": "1 (mm/s) = 1e-3 (m/s)"
          },
          "velocity_candidate": {
            "exported_key": "c_mm_per_s",
            "identity": "1 (kHz)/(um^-1) = 1 (mm/s)",
            "quantity": "c",
            "units": "mm/s"
          }
        },
        "rule_id": "unit_chain_v1",
        "sound": {
          "assumptions": [
            "derived_from_frozen_distance_time_points_only"
          ],
          "input": {
            "exported_key": "c_m_per_s",
            "quantity": "sound_speed",
            "units": "m/s"
          }
        }
      },
      "criterion": {
        "criterion_id": "lowk_velocity_ratio_v1",
        "eps": 1e-12,
        "metric": "rel_err = abs(v_bragg_m_per_s - v_sound_m_per_s) / max(abs(v_sound_m_per_s), eps)",
        "prerequisites": [
          "unit_labels_pinned_in_upstream_records",
          "explicit_cross_lane_pairing_present"
        ],
        "rationale": "Pinned conservative tolerance for numeric comparability after explicit unit conversion; no systematic-error model.",
        "tolerance": 0.15
      },
      "derived": {
        "abs_diff_m_per_s": null,
        "bragg_velocity_candidate_m_per_s": 0.0009729313348425234,
        "bragg_velocity_candidate_se_m_per_s": 0.00016012340869413268,
        "pass": null,
        "rel_err": null,
        "sound_velocity_m_per_s": 0.0014298851656085652,
        "sound_velocity_se_m_per_s": 0.0002711314608466893,
        "z_score": null
      },
      "mapping_tuple_id": null,
      "pair_id": "br04b_conditionB__snd02_single",
      "pair_type": "none",
      "sound_key": "snd02_single",
      "source_locators": {
        "bragg": {
          "fingerprint": "35d592ba9bc9ca487c93d12f32e1bac967531c2159e37abd062ec8fb6830f9b4",
          "lock_path": "formal/markdown/locks/observables/OV-BR-04B_bragg_lowk_slope_conditionB.md",
          "schema": "OV-BR-04B_bragg_lowk_slope_conditionB/v2",
          "source": {
            "figure": "Fig. 2",
            "page_render": "page6_z4.png",
            "pdf_relpath": "formal/external_evidence/bec_bragg_shammass_2012/source.pdf",
            "pdf_sha256": "ef5416e243b0863dada51b68483b72edf83e3b3870bf417b9215b236ea61207c",
            "png_relpath": "formal/external_evidence/bec_bragg_shammass_2012/page_renders/page6_z4.png",
            "png_sha256": "54f38f343e3e3bb329fdaf539ed9e0ea2ed0dc87667b4afc981263f6845002ed"
          }
        },
        "regime": {
          "fingerprint": "3bb051329ae22c1f9649cca702f26c4cbe4adf8adcbc84cf0d9e79f880e5e8ac",
          "lock_path": "formal/markdown/locks/observables/OV-BR-02_regime_bridge_record.md",
          "schema": "OV-BR-02/v1"
        },
        "sound": {
          "fingerprint": "1e1e1f09907117e081fb9be9cab34d39884cf66acc8e2811d807e0a2db7a1dbe",
          "lock_path": "formal/markdown/locks/observables/OV-SND-02_sound_speed_from_propagation.md",
          "schema": "OV-SND-02_sound_speed_from_propagation/v1"
        }
      },
      "values": {
        "bragg_se": 0.16012340869413266,
        "bragg_value": 0.9729313348425234,
        "bragg_velocity_candidate_units": "mm_per_s",
        "sound_c_units": "m_per_s",
        "sound_se": 0.0002711314608466893,
        "sound_value": 0.0014298851656085652
      }
    },
    {
      "bragg_key": "br04b_conditionB",
      "comparability": {
        "notes": "Comparison is only computed when an explicit cross-lane pairing exists; otherwise prerequisites are reported only.",
        "reason_codes": [
          "CONVERSION_CHAIN_PINNED",
          "CRITERION_DEFINED",
          "OUTSIDE_TOL"
        ],
        "status": "fail"
      },
      "conversion_chain": {
        "bragg": {
          "assumptions": [
            "uses_unit_identities_pinned_in_OV-BR-04A/B",
            "no_additional_physical_equivalence_claim"
          ],
          "input": {
            "quantity": "low_k_slope_of_omega_over_2pi_vs_k",
            "slope_units": "(kHz)/(um^-1)",
            "x_units": "um^-1",
            "y_units": "kHz"
          },
          "to_m_per_s": {
            "factor": 0.001,
            "identity": "1 (mm/s) = 1e-3 (m/s)"
          },
          "velocity_candidate": {
            "exported_key": "c_mm_per_s",
            "identity": "1 (kHz)/(um^-1) = 1 (mm/s)",
            "quantity": "c",
            "units": "mm/s"
          }
        },
        "rule_id": "unit_chain_v1",
        "sound": {
          "assumptions": [
            "derived_from_frozen_distance_time_points_only"
          ],
          "input": {
            "exported_key": "c_m_per_s",
            "quantity": "sound_speed",
            "units": "m/s"
          }
        }
      },
      "criterion": {
        "criterion_id": "lowk_velocity_ratio_v1",
        "eps": 1e-12,
        "metric": "rel_err = abs(v_bragg_m_per_s - v_sound_m_per_s) / max(abs(v_sound_m_per_s), eps)",
        "prerequisites": [
          "unit_labels_pinned_in_upstream_records",
          "explicit_cross_lane_pairing_present"
        ],
        "rationale": "Pinned conservative tolerance for numeric comparability after explicit unit conversion; no systematic-error model.",
        "tolerance": 0.15
      },
      "derived": {
        "abs_diff_m_per_s": 0.0005654202682970807,
        "bragg_velocity_candidate_m_per_s": 0.0009729313348425234,
        "bragg_velocity_candidate_se_m_per_s": 0.00016012340869413268,
        "pass": false,
        "rel_err": 0.36754943872592,
        "sound_velocity_m_per_s": 0.001538351603139604,
        "sound_velocity_se_m_per_s": 0.0001698139946589455,
        "z_score": 2.4225211407042813
      },
      "mapping_tuple_id": null,
      "pair_id": "br04b_conditionB__snd02b_seriesB",
      "pair_type": "cross_source_hypothesis",
      "sound_key": "snd02b_seriesB",
      "source_locators": {
        "bragg": {
          "fingerprint": "35d592ba9bc9ca487c93d12f32e1bac967531c2159e37abd062ec8fb6830f9b4",
          "lock_path": "formal/markdown/locks/observables/OV-BR-04B_bragg_lowk_slope_conditionB.md",
          "schema": "OV-BR-04B_bragg_lowk_slope_conditionB/v2",
          "source": {
            "figure": "Fig. 2",
            "page_render": "page6_z4.png",
            "pdf_relpath": "formal/external_evidence/bec_bragg_shammass_2012/source.pdf",
            "pdf_sha256": "ef5416e243b0863dada51b68483b72edf83e3b3870bf417b9215b236ea61207c",
            "png_relpath": "formal/external_evidence/bec_bragg_shammass_2012/page_renders/page6_z4.png",
            "png_sha256": "54f38f343e3e3bb329fdaf539ed9e0ea2ed0dc87667b4afc981263f6845002ed"
          }
        },
        "regime": {
          "fingerprint": "3bb051329ae22c1f9649cca702f26c4cbe4adf8adcbc84cf0d9e79f880e5e8ac",
          "lock_path": "formal/markdown/locks/observables/OV-BR-02_regime_bridge_record.md",
          "schema": "OV-BR-02/v1"
        },
        "sound": {
          "fingerprint": "20847369ccb9572fda4fac8101ed61937ad10ca9e245567fa9c27344aea04810",
          "lock_path": "formal/markdown/locks/observables/OV-SND-02B_sound_speed_from_propagation_seriesB.md",
          "schema": "OV-SND-02B_sound_speed_from_propagation_seriesB/v1"
        }
      },
      "values": {
        "bragg_se": 0.16012340869413266,
        "bragg_value": 0.9729313348425234,
        "bragg_velocity_candidate_units": "mm_per_s",
        "sound_c_units": "m_per_s",
        "sound_se": 0.0001698139946589455,
        "sound_value": 0.001538351603139604
      }
    }
  ],
  "schema": "OV-BR-SND-03_cross_lane_lowk_consistency_audit/v4",
  "sound_date": "2026-01-24",
  "source_locators": {
    "bragg": {
      "br03n_lock_path": "formal/markdown/locks/observables/OV-BR-03_bragg_dispersion_k_omega_digitized.md",
      "br04a_lock_path": "formal/markdown/locks/observables/OV-BR-04A_bragg_lowk_slope_conditionA.md",
      "br04b_lock_path": "formal/markdown/locks/observables/OV-BR-04B_bragg_lowk_slope_conditionB.md"
    },
    "regime": {
      "br02_lock_path": "formal/markdown/locks/observables/OV-BR-02_regime_bridge_record.md"
    },
    "sound": {
      "snd02_lock_path": "formal/markdown/locks/observables/OV-SND-02_sound_speed_from_propagation.md",
      "snd02b_lock_path": "formal/markdown/locks/observables/OV-SND-02B_sound_speed_from_propagation_seriesB.md"
    }
  },
  "status": {
    "blocked": false,
    "blockers": [],
    "inputs": {
      "admissibility_manifest": {
        "path": "formal/markdown locks/gates/admissibility_manifest_ENABLED_OVERRIDE.json",
        "version": 5
      },
      "mapping_tuples": {
        "ovbr_snd02_density_mapping": {
          "exists": true,
          "parse_error": null,
          "relpath": "formal/external_evidence/bec_sound_density_secondary_TBD/ovbr_snd02_density_mapping/mapping_tuples.json",
          "schema": "OV-BR-SND-02_explicit_cross_source_density_mapping_tuples/v4"
        },
        "ovbr_snd03_bragg_sound_pairing": {
          "bragg_sound_mapping_present": true,
          "bragg_sound_tuple_count": 2,
          "exists": true,
          "parse_error": null,
          "relpath": "formal/external_evidence/bec_bragg_sound_pairing_TBD/ovbr_snd03_bragg_sound_mapping/mapping_tuples.json",
          "schema": "OV-BR-SND-03_explicit_bragg_sound_pairing_tuples/v4"
        }
      },
      "required_gates": [
        "CT01",
        "SYM01",
        "CAUS01"
      ],
      "sound_seriesB_blocked": false
    }
  },
  "status_date": "2026-01-25"
}
```

Record fingerprint: `34e6c6c6c0a7598a316273eba3295999632e36bc36442a6993de89859884d2db`
