# OV-BM-01N — Digitized benchmark: mean-field mean-shift vs peak density (computed)

Scope / limits
- Benchmark-only numeric ingestion; no physics validation claim
- No fitting; no regime averaging; no continuity claim; no cross-observable inference

Record (computed)

```json
{
  "dataset": {
    "columns": [
      {
        "dtype": "float",
        "name": "peak_density_1e14_cm3",
        "unit": "1e14 cm^-3"
      },
      {
        "dtype": "float",
        "name": "delta_nu_khz",
        "unit": "kHz"
      },
      {
        "dtype": "float",
        "name": "delta_nu_err_khz",
        "unit": "kHz"
      }
    ],
    "csv_relpath": "formal/external_evidence/bec_bragg_stenger_1999/ovbm01_digitization/mean_shift_vs_peak_density.csv",
    "csv_sha256": "3f4103ce4ea0dc94bf48f3fc27691d590682666e27b931e761a9e1303fb88c0e",
    "metadata_relpath": "formal/external_evidence/bec_bragg_stenger_1999/ovbm01_digitization/mean_shift_vs_peak_density.metadata.json",
    "row_count": 9
  },
  "date": "2026-01-23",
  "digitization_id": "OV-BM-01N",
  "fingerprint": "bed12796e7427943b998f80ad5eb7de37dbcb26dd11c902e119b5a88b6210eb3",
  "observable_id": "OV-BM-01",
  "schema": "OV-BM-01_mean_field_line_shift_scaling_digitized/v1",
  "scope_limits": [
    "benchmark_only_numeric",
    "no_curve_fitting",
    "no_regime_averaging",
    "no_continuity_claim",
    "no_cross_observable_inference",
    "non_decisive_by_design"
  ],
  "source": {
    "arxiv_pdf_relpath": "formal/external_evidence/bec_bragg_stenger_1999/9901109v1.pdf",
    "arxiv_pdf_sha256": "69b8698846a142cb7a404aaf6e8b8d24698e5cbfc06bc16f96f70b09074d5c51",
    "citation": "Stenger et al. (1999) \u2014 Bragg spectroscopy of a Bose\u2013Einstein condensate",
    "digitization_method": "manual_transcription_from_pinned_screenshot",
    "figure": "Fig. 4 (panel a)",
    "notes": "Smallest acceptable target under BM-DIG-01; values are approximate and intended for pipeline determinism checks only.",
    "screenshot_relpath": "formal/external_evidence/bec_bragg_stenger_1999/Screenshot 2026-01-23 234806.png",
    "screenshot_sha256": "8740b31ca2cff222b2d81a980d7d43bac6bf0cb01be07da6858428326b07f365",
    "series": "filled_circles_only"
  }
}
```

Record fingerprint: `bed12796e7427943b998f80ad5eb7de37dbcb26dd11c902e119b5a88b6210eb3`
