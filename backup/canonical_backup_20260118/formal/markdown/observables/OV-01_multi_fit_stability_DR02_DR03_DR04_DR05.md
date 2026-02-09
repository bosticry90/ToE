# OV-01d Multi-Fit Stability (DR-02a vs DR-03a vs DR-04a vs DR-05a)

Date: 2026-01-17

This report extends OV-01c to a 4-fit robustness envelope using:

- DR-02a: `dr01_fit_artifact.json` (k <= 3.2 um^-1)
- DR-03a: `dr03_fit_artifact.json` (k <= 2.1 um^-1)
- DR-05a: `dr05_fit_artifact.json` (k <= 1.8 um^-1)
- DR-04a: `dr04_fit_artifact.json` (k <= 1.6 um^-1)

OV-01 observable definition (Option A):

- obs = g * c_s^2(metric)

Multi-fit residuals use the same normalized form as OV-01b, now pairwise:

- R_ij = |obs_i - obs_j| / max(|obs_i|, |obs_j|, eps)

Summary statistics:

- R_max = max(R_ij)
- R_rms = sqrt(mean(R_ij^2))

Gate (provisional): retain iff R_max <= tau_obs, with tau_obs = 0.10.

## Fit-derived values

Squared values (c_s^2):

- DR-02a c_s^2 = 4.7914675051252575e-06
- DR-03a c_s^2 = 4.4358017089341570e-06
- DR-05a c_s^2 = 3.9704020017189680e-06
- DR-04a c_s^2 = 3.4017829332315543e-06

## Pairwise normalized residuals (independent of g for g != 0)

Index ordering used here: 02=0, 03=1, 04=2, 05=3.

- R_02_03 = 0.07422899055678828
- R_02_04 = 0.29003318302945985
- R_02_05 = 0.17135992314004556
- R_03_04 = 0.23310752904485865
- R_03_05 = 0.1049189611604655
- R_04_05 = 0.14321448262448797

Summary:

- R_max = 0.29003318302945985
- R_rms = 0.1847750479626659

## Interpretation (monotone drift vs outlier)

- c_s (and thus c_s^2) decreases monotonically as k-max shrinks (3.2 → 2.1 → 1.8 → 1.6).
- DR-05a sits between DR-03a and DR-04a, supporting a smooth drift interpretation rather than DR-04a being a single isolated outlier.
- Under tau_obs = 0.10, the gate still fails (R_max ≈ 0.29), reinforcing that strict linear-through-origin low-k linearization is not robust across these windows.

Next escalation (queued): introduce a curvature-aware DR fit method tag (e.g., omega/k ≈ c_s + β k^2) and test whether the multi-fit envelope collapses while remaining deterministic and data-backed.
