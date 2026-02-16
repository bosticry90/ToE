# CT-08 External Anchor Dispersion High-k Slice v0

Status: Pinned (v0)

Purpose
- Establish a high-k external-anchor comparator using a pinned slice rule.
- Probe the complementary regime while remaining explicit about non-independence from CT-06.
- Keep claim scope bounded to deterministic dataset-conditional reproducibility only.

Statement (bounded external anchor)
- Given `Steinhauer2001_Fig3a_Digitized_v1` and pinned preprocessing assumptions, the same pinned model family must reproduce the high-k slice observable `omega_over_2pi_kHz_vs_k_um_inv` within CT-08 tolerances; otherwise it fails.

Non-independence declaration
- `non_independent_of_CT06`: CT-08 uses the same origin dataset as CT-06 with a deterministic slice rule.

Dataset anchor
- Origin dataset identifier: `Steinhauer2001_Fig3a_Digitized_v1`.
- Origin dataset path: `formal/external_evidence/bec_bragg_steinhauer_2001/omega_k_data.csv`.

Pinned slicing rule
- Slice mode: high-k quantile.
- `k_quantile = 0.50`.
- `k_min_um_inv` is computed deterministically from the origin dataset and then applied as `k_um_inv >= k_min_um_inv`.

Pinned preprocessing assumptions
- Read typed columns from origin CSV.
- Drop non-finite rows.
- Sort rows by `k_um_inv` ascending.
- Apply pinned high-k slice filter.
- Keep units unchanged (`k` in um^-1, `omega/2pi` in kHz).

Controls (expectation-aware)
- Positive control: least-squares fit on `omega^2 = c_s2*k^2 + alpha*k^4` on the high-k slice.
- Negative control: apply pinned model break (`alpha_scale_negative = 0.5`) and require explicit failure detection.

Pinned tolerances and pass/fail semantics
- `eps_rmse_kHz = 0.25`.
- `eps_max_abs_error_kHz = 0.50`.
- `eps_reduced_chi2 = 4.0`.
- Positive control passes when all tolerance checks are satisfied.
- Negative control passes only when at least one tolerance is violated and the failure is detected.

Required vocabulary
- CT-08
- external anchor
- dispersion
- Steinhauer2001_Fig3a_Digitized_v1
- high-k slice
- k_um_inv
- k_min_um_inv
- positive control
- negative control
- eps_rmse_kHz
- eps_max_abs_error_kHz
- eps_reduced_chi2
- non_independent_of_CT06
