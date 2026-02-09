# SND-DIG-01 — Minimal density digitization acceptance criteria (computed)

Scope / limits
- Bookkeeping / workflow governance only; no physics claim
- Specifies smallest acceptable density digitization target and acceptance criteria

Record (computed)

```json
{
  "acceptance_criteria": [
    "Source provenance must name paper and page context (and figure/table if applicable).",
    "Digitized density must be stored as a frozen CSV (or equivalent) with explicit units.",
    "Digitization must be deterministic (no RNG) and reproducible from pinned inputs in the repo (PDF snapshot).",
    "First pass may include a single condition only; if multiple conditions are available, they must be stored without averaging.",
    "The resulting numeric record must assert: non-decisive by design, no continuity claim, no regime averaging, no cross-observable inference.",
    "A new OV-SEL-SND-style narrative lock must state: what changed / what did not / why, and must explicitly confirm no policy/threshold changes were triggered."
  ],
  "allowed_targets": [
    {
      "lane": "sound",
      "minimal_target": "Extract a single explicitly stated density value (central or peak), with units, from a pinned source PDF snapshot used by the sound lane. Store as a frozen CSV plus JSON metadata wrapper under formal/external_evidence.",
      "name": "Central (or peak) density numeric anchor",
      "target_id": "OV-SND-03N",
      "what_it_tests": [
        "typed numeric artifact ingestion",
        "unit/provenance preservation",
        "density as second independent variable (without implying dependence)"
      ]
    }
  ],
  "date": "2026-01-24",
  "explicit_disallow": [
    "no continuity inference from density",
    "no regime crossover claim",
    "no averaging across regimes",
    "no selection preference flip attributable to density ingestion",
    "no density imputation from unrelated observables"
  ],
  "fingerprint": "3e2879d90d82ba8b420d39538a9b8b609cd5d1f52f8cac41de43fefdb294f973",
  "narrative": "SND-DIG-01 minimal density digitization plan (bookkeeping-only):\n- Choose a pinned sound-lane source PDF already in the repo.\n- Extract at least one explicit density number with units, deterministically.\n- Store as frozen artifact + metadata; do not fit; do not infer dependence.\n- Lock an OV-SEL-SND-style narrative confirming no policy triggers or preference changes occurred.",
  "schema": "SND-DIG-01_minimal_density_digitization/v1",
  "scope_statement": "Sound-lane density digitization: frozen density anchor(s) for bookkeeping-scale checks. No validation claim; no continuity inference; no regime averaging; no cross-observable inference."
}
```

Record fingerprint: `3e2879d90d82ba8b420d39538a9b8b609cd5d1f52f8cac41de43fefdb294f973`
