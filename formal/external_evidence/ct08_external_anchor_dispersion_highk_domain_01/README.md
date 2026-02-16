# CT-08 External Anchor Dispersion High-k Domain 01

Contents
- `dataset_metadata.json`
- `source_citation.md`
- `ct08_reference_report.json`
- `ct08_candidate_report.json`

Origin dataset
- `formal/external_evidence/bec_bragg_steinhauer_2001/omega_k_data.csv`

Pinned slicing
- `k_quantile = 0.50`
- Keep points satisfying `k_um_inv >= k_min_um_inv`
- `k_min_um_inv` computed deterministically from origin CSV

Determinism
- Front door: `.\py.ps1 -m formal.python.tools.ct08_external_anchor_dispersion_highk_front_door`
- Comparator lock check: `.\py.ps1 -m pytest formal/python/tests/test_ct08_external_anchor_dispersion_highk_slice_v0_lock.py -q`

