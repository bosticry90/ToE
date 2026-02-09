# OV-SND-03N2 — Secondary-source multi-density conditions (computed)

Scope / limits
- Bookkeeping only; no physics claim
- Remains blocked until a pinned secondary PDF + frozen multi-row density table exist
- No implied condition identity across sources

Record (computed)

```json
{
  "dataset": {
    "columns": [
      {
        "dtype": "string",
        "name": "density_condition_key",
        "unit": "(label)"
      },
      {
        "dtype": "float",
        "name": "n0_cm3",
        "unit": "cm^-3"
      },
      {
        "dtype": "string",
        "name": "source_locator",
        "unit": "(locator)"
      },
      {
        "dtype": "string",
        "name": "notes",
        "unit": "(text)"
      }
    ],
    "csv_relpath": "formal/external_evidence/bec_sound_density_secondary_TBD/ovsnd03n2_density_digitization/density_conditions.csv",
    "csv_sha256": "0ba69ce88ecf7814813e243b6fcefffb19e4aa58ee74f81627b1e461dbceb025",
    "metadata_relpath": "formal/external_evidence/bec_sound_density_secondary_TBD/ovsnd03n2_density_digitization/density_conditions.metadata.json",
    "row_count": 2,
    "rows_preview": [
      {
        "density_condition_key": "sk98_mu_digitized_01",
        "n0_cm3": 565116912536000.0,
        "source_locator": "png_digitization:C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_sound_density_secondary_TBD/Screenshot 2026-01-24 153305.png::panel_b_mu:px=391,py=157,mu_over_kb_uK=0.412065"
      },
      {
        "density_condition_key": "sk98_mu_digitized_02",
        "n0_cm3": 503058081411000.0,
        "source_locator": "png_digitization:C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_sound_density_secondary_TBD/Screenshot 2026-01-24 153305.png::panel_b_mu:px=406,py=162,mu_over_kb_uK=0.366814"
      }
    ]
  },
  "date": "2026-01-24",
  "fingerprint": "1b79934c23c803991487f9be9989ba880d3ee412779bd4049d07d66a4edd7dd5",
  "observable_id": "OV-SND-03N2",
  "schema": "OV-SND-03N2_secondary_density_conditions_digitized/v1",
  "scope_limits": [
    "bookkeeping_only",
    "no_physics_claim",
    "no_condition_identity_assumption",
    "no_imputation",
    "no_continuity_claim",
    "non_decisive_by_design"
  ],
  "source": {
    "notes": "This is the governance-safe ingestion point for a secondary multi-density source. It does not fabricate density values; it remains blocked until a pinned PDF and a frozen multi-row table exist.",
    "secondary_pdf_metadata_relpath": "formal/external_evidence/bec_sound_density_secondary_TBD/source.metadata.json",
    "secondary_pdf_relpath": "formal/external_evidence/bec_sound_density_secondary_TBD/source.pdf",
    "secondary_pdf_sha256": "f16b43d97bf3ed51ff9d51043677a2960145f46797c48e0a11c562048de568c7"
  },
  "status": {
    "blocked": false,
    "blockers": []
  }
}
```

Record fingerprint: `1b79934c23c803991487f9be9989ba880d3ee412779bd4049d07d66a4edd7dd5`
