# Secondary density source (TBD)

This folder is intentionally a placeholder for the **secondary density source**
needed to unblock OV-BR-SND-02 and OV-SND-04.

Required files (expected)
- `source.pdf` (the pinned PDF that contains **multiple explicit density conditions**)
- Optional: `source_page_screenshots/` (PNG renders of the pages/regions used for digitization)

Recommended workflow
1. Place `source.pdf` here.
2. If you are digitizing from a table/figure image, place deterministic page renders under `source_page_screenshots/`.
3. Use the helper tool `formal/python/tools/pin_external_evidence_metadata.py` to generate `source.metadata.json` with sha256 hashes.

Notes
- Do not proceed with cross-source mapping unless the PDF is pinned and hashed.
- Do not infer condition identity across sources; mapping must be explicit.
