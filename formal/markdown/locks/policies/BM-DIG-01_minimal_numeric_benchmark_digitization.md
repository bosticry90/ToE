# BM-DIG-01 — Minimal numeric benchmark digitization acceptance criteria (computed)

Scope / limits
- Bookkeeping / workflow governance only; no physics claim
- Specifies smallest acceptable digitization target and acceptance criteria

Record (computed)

```json
{
  "acceptance_criteria": [
    "Source provenance must name paper, figure number, and (if available) page/axis labels.",
    "Digitized data must be stored as a frozen CSV (or equivalent) with explicit units for every axis.",
    "Digitization must be deterministic (no RNG) and reproducible from a pinned input image/PDF snapshot in the repo.",
    "One series only for the first pass (no mixing multiple curves, no insets).",
    "Minimum point count: N>=8 covering >=60% of the visible x-range for that series.",
    "No fitting as part of the benchmark digitization step; fitting remains a separate, explicitly-scoped operation.",
    "The resulting benchmark numeric record must assert: non-decisive by design, no continuity claim, no regime averaging, no cross-observable inference.",
    "A new OV-SEL-BM-style narrative lock must state: what changed / what did not / why, and must explicitly confirm no policy/threshold changes were triggered."
  ],
  "allowed_targets": [
    {
      "benchmark_id": "OV-BM-01",
      "minimal_target": "Digitize a single curve/series that reports mean (first-moment) frequency shift as a function of density (or a directly stated density proxy) from one figure in Stenger (1999).",
      "name": "Mean-field mean-shift scaling",
      "what_it_tests": [
        "typed numeric artifact ingestion",
        "unit/provenance preservation",
        "no model selection from benchmark",
        "no regime blending"
      ]
    },
    {
      "benchmark_id": "OV-BM-02",
      "minimal_target": "Digitize a single curve/series sufficient to represent a linewidth quantity and its stated decomposition components (as available) from one figure in Stenger (1999); store components separately if the figure reports them separately.",
      "name": "Linewidth quadrature composition",
      "what_it_tests": [
        "multiple component storage without forced averaging",
        "quadrature structure preserved",
        "no dominance/crossover claims inferred"
      ]
    }
  ],
  "date": "2026-01-23",
  "explicit_disallow": [
    "no sound-speed inference",
    "no dispersion-family inference",
    "no preference flips attributable to benchmark ingestion",
    "no continuity or regime crossover claim",
    "no averaging across regimes",
    "no numeric comparison used as ToE validation evidence"
  ],
  "fingerprint": "b018182558b7e8dd4daebf64099b948fb96e28ab927d8c9df6d2d9e55a10c181",
  "narrative": "BM-DIG-01 minimal numeric benchmark digitization plan (bookkeeping-only):\n- Choose exactly one benchmark (OV-BM-01 or OV-BM-02).\n- Digitize exactly one series from exactly one figure, with explicit provenance and units.\n- Store as a frozen artifact; do not fit; do not infer; do not blend regimes.\n- Lock an OV-SEL-BM-style narrative confirming no policy triggers or preference changes occurred.",
  "schema": "BM-DIG-01_minimal_numeric_benchmark_digitization/v1",
  "scope_statement": "Benchmark-only numeric digitization: frozen artifact ingestion stress test. No validation claim; no continuity inference; no regime averaging; no cross-observable inference."
}
```

Record fingerprint: `b018182558b7e8dd4daebf64099b948fb96e28ab927d8c9df6d2d9e55a10c181`
