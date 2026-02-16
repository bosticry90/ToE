# CT-08 Dispersion High-k Slice Citation

Dataset ID: `Steinhauer2001_Fig3a_Digitized_v1_highk_slice_v0`

Origin source
- Steinhauer et al., `cond-mat/0111438`, Fig. 3(a).
- Origin CSV: `formal/external_evidence/bec_bragg_steinhauer_2001/omega_k_data.csv`.

Slice provenance
- Deterministic transformation: keep rows with `k_um_inv >= quantile(k_um_inv, 0.5)`.
- Additional transformations: finite-row filter and ascending k sort.
- Numeric edits: none.

Governance scope
- `non_independent_of_CT06` is explicit and required for interpretation.
- No external-truth promotion beyond the front-door contract.

