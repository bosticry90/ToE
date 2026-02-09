# OV-BM-01 — Benchmark A: mean-field line shift scaling (symbolic)

Baseline benchmark observable (symbolic, non-validating).

What is locked
- Functional dependency (linear in density)
- Symbolic proportionality form
- First moment (mean shift), not a dispersion curve

What is not locked
- No numerical parameter values
- No digitized points / CSV artifacts
- No fitting, no regime averaging, no continuity claim

Record (computed)

```json
{
  "category": "Benchmark",
  "functional_dependency": {
    "is_proportional": true,
    "linear_in": [
      "n0"
    ],
    "moment": "first_moment_mean_shift",
    "not_a_dispersion_curve": true,
    "variables": {
      "U": "interaction strength (mean-field coupling)",
      "h": "Planck constant",
      "n0": "peak density"
    }
  },
  "notes": "Encodes a benchmark mean-field density\u2013shift dependency used solely to test regime handling and provenance preservation. Does not validate any ToE mechanism or imply continuity across regimes.",
  "observable_id": "OV-BM-01",
  "reference_provenance": {
    "citation": "Stenger et al. (1999) \u2014 Bragg spectroscopy of a Bose\u2013Einstein condensate",
    "role": "calibration_weight_non_validating",
    "type": "literature_reference"
  },
  "schema": "OV-BM-01_mean_field_line_shift_scaling_benchmark/v1",
  "scope_limits": [
    "symbolic_only",
    "no_digitization",
    "no_extracted_points",
    "no_curve_fitting",
    "no_regime_averaging",
    "no_continuity_claim",
    "no_cross_observable_inference",
    "non_decisive_by_design"
  ],
  "status": "Structural (symbolic)",
  "symbolic_relation_latex": "\\\\langle \\\\Delta \\\\nu \\\\rangle \\\\propto \\\\frac{4 n_0 U}{7 h}",
  "validation": "None"
}
```

Record fingerprint: `1ee5c6899cb28c404b2ab6c0ae79a6751a2363ddd5fc8b12c6acd0c9c44353b3`
