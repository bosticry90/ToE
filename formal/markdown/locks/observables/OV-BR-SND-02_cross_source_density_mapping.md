# OV-BR-SND-02 — Cross-source density mapping record (computed)

Scope / limits
- Bookkeeping only; no physics claim
- Declares intended mapping structure and current blockers; no continuity/averaging

Record (computed)

```json
{
  "date": "2026-01-24",
  "density_sources": {
    "same_source": {
      "coverage_report": {
        "n_density_conditions_supported": 1,
        "observable_id": "OV-SND-03N-COV",
        "record_fingerprint": "10adc18eda47c61a65702abc6fc6f0f0dad76cb97601a33e4257fc54a95e6525",
        "record_schema": "OV-SND-03N_density_coverage_report/v1"
      },
      "notes": "Pinned sound note provides only one explicit density under current digitization method.",
      "status": "present"
    },
    "secondary_source": {
      "candidate": "Experimental source with multiple explicit density conditions (preferred: same experiment as sound propagation)",
      "expected_repo_location": {
        "density_table_csv": "formal/external_evidence/bec_sound_density_secondary_TBD/ovsnd03n2_density_digitization/density_conditions.csv",
        "density_table_metadata": "formal/external_evidence/bec_sound_density_secondary_TBD/ovsnd03n2_density_digitization/density_conditions.metadata.json",
        "folder": "formal/external_evidence/bec_sound_density_secondary_TBD/",
        "mapping_tuples": "formal/external_evidence/bec_sound_density_secondary_TBD/ovbr_snd02_density_mapping/mapping_tuples.json",
        "metadata": "formal/external_evidence/bec_sound_density_secondary_TBD/source.metadata.json",
        "pdf": "formal/external_evidence/bec_sound_density_secondary_TBD/source.pdf"
      },
      "ingestion_gate": {
        "blocked": false,
        "blockers": [],
        "lock_path": "formal/markdown/locks/observables/OV-SND-03N2_secondary_density_conditions_digitized.md",
        "observable_id": "OV-SND-03N2",
        "record_fingerprint": "1b79934c23c803991487f9be9989ba880d3ee412779bd4049d07d66a4edd7dd5",
        "record_schema": "OV-SND-03N2_secondary_density_conditions_digitized/v1"
      },
      "required_artifacts": [
        "density_conditions.csv (multi-row)",
        "density_conditions.metadata.json (hashes + provenance)",
        "mapping_tuples.json (explicit cross-source mapping tuples)"
      ],
      "status": "present_unblocked"
    }
  },
  "fingerprint": "365869bd6a3ea7b9a0f4afc43aaa234bae28bd289f55866f42b811ddf55c26e4",
  "mapping": {
    "allowed_computations": [
      "compute_OV-SND-04_only_when_mapping_unblocked_and_pairs>=2"
    ],
    "current_blockers": [],
    "forbidden_computations": [
      "many_densities_to_one_speed_key (variant1_nonphysical_unless_explicitly_labeled)",
      "assume_condition_identity_across_sources",
      "impute_missing_density",
      "average_across_regimes",
      "make_continuity_or_universality_claims"
    ],
    "mapping_file": {
      "exists": true,
      "path": "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_sound_density_secondary_TBD/ovbr_snd02_density_mapping/mapping_tuples.json",
      "row_count": 2,
      "schema": "OV-BR-SND-02_explicit_cross_source_density_mapping_tuples/v4",
      "sha256": "a629a44ad9bbd13f94694bd4e2ad9b08de429213f6c420b8af47d11830d4b49d"
    },
    "mapping_is_complete": true,
    "mapping_tuples": [
      {
        "density_condition_key": "central",
        "notes": "Same-source pairing (Andrews 1997).",
        "pair_type": "same_source",
        "propagation_condition_key": "snd02_single",
        "rationale": "Declared pairing for OV-SND-04 constancy bookkeeping; not a claim of same experimental run beyond pinned Andrews source context.",
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
        "density_condition_key": "sk98_mu_digitized_01",
        "notes": "Cross-source tuple (Andrews speed condition \u2194 Stamper-Kurn 1998 density digitization key).",
        "pair_type": "cross_source_hypothesis",
        "propagation_condition_key": "snd02b_seriesB",
        "rationale": "Declared cross-source pairing hypothesis for OV-SND-04; conditional-on-mapping only; no implied condition identity unless separately evidenced.",
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
    "non_mapping_statement": "No cross-source density mapping is asserted at present. This record exists to prevent implicit condition identity. OV-SND-04 must remain blocked unless this mapping is explicitly unblocked and yields >=2 valid pairs.",
    "recognized_density_condition_keys": [
      "central",
      "sk98_mu_digitized_01",
      "sk98_mu_digitized_02"
    ],
    "required_mapping_keys": [
      "propagation_condition_key",
      "density_condition_key",
      "source_locators"
    ],
    "status": "unblocked"
  },
  "schema": "OV-BR-SND-02_cross_source_density_mapping/v1",
  "scope_limits": [
    "bookkeeping_only",
    "no_physics_claim",
    "no_continuity_claim",
    "no_cross_regime_averaging",
    "non_decisive_by_design"
  ],
  "sound_anchor": {
    "available_propagation_condition_keys": [
      "snd02_single",
      "snd02b_seriesB"
    ],
    "primary_speed": {
      "condition_label": "single_condition_from_OV-SND-01N_Fig2_squares_seriesA",
      "observable_id": "OV-SND-02",
      "propagation_condition_key": "snd02_single",
      "record_fingerprint": "1e1e1f09907117e081fb9be9cab34d39884cf66acc8e2811d807e0a2db7a1dbe",
      "record_schema": "OV-SND-02_sound_speed_from_propagation/v1"
    },
    "secondary_speed": {
      "blocked": false,
      "blockers": [],
      "condition_label": "second_condition_from_OV-SND-01N2_seriesB",
      "observable_id": "OV-SND-02B",
      "propagation_condition_key": "snd02b_seriesB",
      "record_fingerprint": "20847369ccb9572fda4fac8101ed61937ad10ca9e245567fa9c27344aea04810",
      "record_schema": "OV-SND-02B_sound_speed_from_propagation_seriesB/v1"
    }
  }
}
```

Record fingerprint: `365869bd6a3ea7b9a0f4afc43aaa234bae28bd289f55866f42b811ddf55c26e4`
