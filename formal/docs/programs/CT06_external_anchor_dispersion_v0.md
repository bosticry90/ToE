# CT-06 External Anchor Dispersion v0

Status: Pinned (v0)

Purpose
- Establish the first external anchor lane for conditional theorems using a pinned public dispersion dataset.
- Convert public digitized evidence into a deterministic front-door report with explicit pass/fail semantics.
- Keep claim scope bounded to dataset-conditional reproducibility only.

Statement (bounded external anchor)
- Given dataset `Steinhauer2001_Fig3a_Digitized_v1` and pinned preprocessing assumptions, a candidate dispersion model must reproduce the observable `omega_over_2pi_kHz_vs_k_um_inv` within pinned tolerances; otherwise it fails.

Dataset anchor (in-repo CSV)
- Dataset identifier: `Steinhauer2001_Fig3a_Digitized_v1`.
- Dataset path: `formal/external_evidence/ct06_external_anchor_dispersion_domain_01/dispersion_anchor_steinhauer_fig3a_omega_k.csv`.
- Citation string: `Steinhauer et al., cond-mat/0111438, Fig. 3(a)`.

Pinned preprocessing assumptions
- Keep columns: `k_um_inv`, `omega_over_2pi_kHz`, `sigma_omega_over_2pi_kHz`.
- Drop non-finite rows.
- Sort rows by `k_um_inv` ascending.
- Keep units unchanged (`k` in um^-1, `omega/2pi` in kHz).
- Use full pinned row set without stochastic subsampling.

Observable definition
- `omega_over_2pi_kHz_vs_k_um_inv` on the pinned `k` grid from the dataset.

Controls (expectation-aware)
- Positive control: least-squares fit on `omega^2 = c_s2*k^2 + alpha*k^4` on the pinned grid.
- Negative control: apply pinned model break (`alpha_scale_negative = 0.5`) and require explicit failure detection.

Pinned tolerances and pass/fail semantics
- `eps_rmse_kHz = 0.25`.
- `eps_max_abs_error_kHz = 0.50`.
- `eps_reduced_chi2 = 4.0`.
- Positive control passes when all tolerance checks are satisfied.
- Negative control passes only when at least one tolerance is violated and the failure is detected.

Required vocabulary
- CT-06
- external anchor
- dispersion
- Steinhauer2001_Fig3a_Digitized_v1
- preprocessing assumptions
- omega_over_2pi_kHz_vs_k_um_inv
- positive control
- negative control
- eps_rmse_kHz
- eps_max_abs_error_kHz
- eps_reduced_chi2
