# CT-06 External Anchor Dispersion Domain 01

Contents
- `dispersion_anchor_steinhauer_fig3a_omega_k.csv`
- `dataset_metadata.json`
- `source_citation.md`
- `ct06_reference_report.json`
- `ct06_candidate_report.json`

Pinned preprocessing
- Keep columns `k_um_inv`, `omega_over_2pi_kHz`, `sigma_omega_over_2pi_kHz`.
- Drop non-finite rows.
- Sort by `k_um_inv` ascending.
- Keep native units (um^-1, kHz).

Determinism
- Front door: `.\py.ps1 -m formal.python.tools.ct06_external_anchor_dispersion_front_door`
- Comparator lock check: `.\py.ps1 -m pytest formal/python/tests/test_ct06_external_anchor_dispersion_v0_lock.py -q`

