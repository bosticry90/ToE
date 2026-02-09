# OV-BM-02 — Benchmark B: linewidth quadrature composition (symbolic)

Baseline benchmark observable (symbolic, non-validating).

What is locked
- Quadrature composition structure (sum of squares)
- Separation of mechanism contributions

What is not locked
- No numerical linewidths
- No dominance/crossover claims
- No digitized points / CSV artifacts
- No fitting, no regime averaging, no continuity claim

Record (computed)

```json
{
  "category": "Benchmark",
  "mechanism_components": {
    "components": [
      {
        "meaning": "Doppler / finite-size broadening",
        "name": "sigma_Doppler"
      },
      {
        "meaning": "mean-field broadening",
        "name": "sigma_MF"
      }
    ],
    "quadrature": true,
    "separation_of_mechanisms": true
  },
  "notes": "Encodes a benchmark linewidth composition rule used to test whether the framework preserves independent contributions without forced averaging or regime blending.",
  "observable_id": "OV-BM-02",
  "reference_provenance": {
    "citation": "Stenger et al. (1999) \u2014 Bragg spectroscopy of a Bose\u2013Einstein condensate",
    "role": "calibration_weight_non_validating",
    "type": "literature_reference"
  },
  "schema": "OV-BM-02_linewidth_quadrature_composition_benchmark/v1",
  "scope_limits": [
    "symbolic_only",
    "no_digitization",
    "no_extracted_points",
    "no_curve_fitting",
    "no_dominance_claim",
    "no_regime_averaging",
    "no_continuity_claim",
    "no_cross_observable_inference",
    "non_decisive_by_design"
  ],
  "status": "Structural (symbolic)",
  "symbolic_relation_latex": "\\\\sigma_{\\\\mathrm{total}}^2 = \\\\sigma_{\\\\mathrm{Doppler}}^2 + \\\\sigma_{\\\\mathrm{MF}}^2",
  "validation": "None"
}
```

Record fingerprint: `0e32eee80d2065f24f99ab1524c76cb5a8deeb7d4372ac9986651d75d5c38b4e`
