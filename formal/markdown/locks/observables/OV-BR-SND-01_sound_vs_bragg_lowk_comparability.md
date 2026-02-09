# OV-BR-SND-01 — Sound vs low-k Bragg comparability (computed)

Scope / limits
- Bookkeeping only; no physics claim
- Declares comparability conditions and current blockers; no continuity/averaging

Record (computed)

```json
{
  "bragg_anchor": {
    "dataset": "DS-02 (low-k)",
    "notes": "OV-BR-05 exports c_mm_per_s derived from locked OV-BR-04A/04B; no additional equivalence is asserted here.",
    "observable_id": "OV-BR-05",
    "quantity": "velocity_candidate_c",
    "units": "mm/s (convertible to m/s via pinned unit identity)"
  },
  "comparability": {
    "comparable_in_principle": true,
    "conditional_notes": [
      "No physics claim: this record only declares governance conditions for comparison.",
      "Quantitative comparison remains fail-closed unless an explicit Bragg\u2194Sound pairing tuple is declared (OV-BR-SND-03 mapping tuples).",
      "Downstream density-dependent checks remain governed by OV-BR-SND-02; this record does not infer density n."
    ],
    "current_blockers": [],
    "forbidden_behaviors": [
      "no_cross_regime_averaging",
      "no_continuity_claim",
      "no_density_inference",
      "no_parameter_matching_without_pinned_calibration"
    ],
    "non_comparability_statement": "A quantitative sound-vs-Bragg comparison is only performed under explicit pairing and audit gates. This record declares the conditions for comparability and forbids implicit averaging or density inference.",
    "principle_conditions": [
      "phonon_regime_low_k",
      "same_definition_of_c (group_velocity at k\u21920)",
      "explicit_density_and_geometry_calibration (no hidden averaging)",
      "explicit_cross_lane_pairing_present (no implicit condition identity)"
    ],
    "status": "not_compared_quantitatively"
  },
  "date": "2026-01-24",
  "fingerprint": "6487a1673c71952663f2cffed0d7384f996885ff6875d67c842f5a51be7df718",
  "schema": "OV-BR-SND-01_sound_vs_bragg_lowk_comparability/v1",
  "scope_limits": [
    "bookkeeping_only",
    "no_physics_claim",
    "no_continuity_claim",
    "no_cross_regime_averaging",
    "non_decisive_by_design"
  ],
  "sound_anchor": {
    "extraction": "slope_from_distance_time_points",
    "observable_id": "OV-SND-02",
    "quantity": "sound_speed_c",
    "record_fingerprint": "1e1e1f09907117e081fb9be9cab34d39884cf66acc8e2811d807e0a2db7a1dbe",
    "record_schema": "OV-SND-02_sound_speed_from_propagation/v1",
    "units": "m/s"
  }
}
```

Record fingerprint: `6487a1673c71952663f2cffed0d7384f996885ff6875d67c842f5a51be7df718`
