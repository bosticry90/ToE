# OV-SND-03N-COV — Density coverage report (computed)

Scope / limits
- Bookkeeping only; no physics claim
- Coverage + blockers only; no new digitization

Record (computed)

```json
{
  "coverage": {
    "density_condition_ids": "from_csv_condition_id_column",
    "density_csv_row_count": 1,
    "speed_condition_ids": "single_condition_OV-SND-02"
  },
  "date": "2026-01-24",
  "decision": {
    "blockers": [
      "density_source_supports_only_one_explicit_condition",
      "speed_anchor_supports_only_one_condition"
    ],
    "multi_condition_possible_same_source": false,
    "n_density_conditions_supported": 1,
    "n_pairs_supported": 1,
    "n_speed_conditions_supported": 1,
    "recommended_path": "OptionB_cross_source_mapping_required"
  },
  "fingerprint": "10adc18eda47c61a65702abc6fc6f0f0dad76cb97601a33e4257fc54a95e6525",
  "inputs": {
    "OV-SND-02": {
      "lock_path": "formal/markdown/locks/observables/OV-SND-02_sound_speed_from_propagation.md",
      "record_fingerprint": "1e1e1f09907117e081fb9be9cab34d39884cf66acc8e2811d807e0a2db7a1dbe",
      "record_schema": "OV-SND-02_sound_speed_from_propagation/v1"
    },
    "OV-SND-03N": {
      "density_csv_relpath": "formal/external_evidence/bec_sound_andrews_1997/ovsnd03_density_digitization/central_density.csv",
      "lock_path": "formal/markdown/locks/observables/OV-SND-03_central_density_digitized.md",
      "record_fingerprint": "d5222e1b706c3c8455e3c0e04f23e14473a04ab2dcff64ba13f266270f8eae7a",
      "record_schema": "OV-SND-03_central_density_digitized/v1"
    }
  },
  "observable_id": "OV-SND-03N-COV",
  "schema": "OV-SND-03N_density_coverage_report/v1",
  "scope_limits": [
    "bookkeeping_only",
    "no_physics_claim",
    "no_new_digitization",
    "no_continuity_claim",
    "non_decisive_by_design"
  ]
}
```

Record fingerprint: `10adc18eda47c61a65702abc6fc6f0f0dad76cb97601a33e4257fc54a95e6525`
