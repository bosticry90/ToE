# CT-07 External Anchor Dispersion Low-k Domain 01

Contents
- `dataset_metadata.json`
- `source_citation.md`
- `ct07_reference_report.json`
- `ct07_candidate_report.json`

Origin dataset
- `formal/external_evidence/bec_bragg_steinhauer_2001/omega_k_data.csv`

Pinned slicing
- `k_quantile = 0.50`
- Keep points satisfying `k_um_inv <= k_max_um_inv`
- `k_max_um_inv` computed deterministically from origin CSV

Determinism
- Front door: `.\py.ps1 -m formal.python.tools.ct07_external_anchor_dispersion_lowk_front_door`
- Comparator lock check: `.\py.ps1 -m pytest formal/python/tests/test_ct07_external_anchor_dispersion_lowk_slice_v0_lock.py -q`

