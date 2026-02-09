# OV-01d Multi-Fit Stability (DR-02a vs DR-03a vs DR-04c vs DR-05a)

Date: 2026-01-18

This report extends OV-01c to a 4-fit robustness envelope using:

- DR-02a: `dr01_fit_artifact.json` (k <= 3.2 um^-1)
- DR-03a: `dr03_fit_artifact.json` (k <= 2.1 um^-1)
- DR-04c: `dr04c_fit_artifact.json` (k <= 2.5 um^-1)
- DR-05a: `dr05_fit_artifact.json` (k <= 1.8 um^-1)

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
- DR-04c c_s^2 = 4.4130067230077940e-06
- DR-05a c_s^2 = 3.9704020017189680e-06

## Pairwise normalized residuals (independent of g for g != 0)

Index ordering used here: 02=0, 03=1, 04c=2, 05=3.

- R_02_03 = 0.07422899055678828
- R_02_04c = 0.07898640274876906
- R_02_05 = 0.17135992314004558
- R_03_04c = 0.005138864949813056
- R_03_05 = 0.10491896116046552
- R_04c_05 = 0.10029550124663272

Summary:

- R_max = 0.17135992314004558
- R_rms = 0.10182223237183996

## Interpretation

Replacing the underpowered DR-04a (k<=1.6, N=4) window with DR-04c (k<=2.5, N=7) reduces the linear-family 4-fit envelope substantially, but it still fails the current τ=0.10 robustness gate.
