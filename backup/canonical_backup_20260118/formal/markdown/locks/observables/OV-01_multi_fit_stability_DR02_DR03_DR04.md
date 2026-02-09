# OV-01c Multi-Fit Stability (DR-02a vs DR-03a vs DR-04a)

Date: 2026-01-17

This report extends OV-01b from a 2-fit cross-check to a 3-fit robustness check using:

- DR-02a: `dr01_fit_artifact.json` (k <= 3.2 um^-1)
- DR-03a: `dr03_fit_artifact.json` (k <= 2.1 um^-1)
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

Sound speeds (m/s):

- DR-02a c_s = 0.0021889420972527477
- DR-03a c_s = 0.0021061343045813002
- DR-04a c_s = 0.0018443922937465213

Squared values (c_s^2):

- DR-02a c_s^2 = 4.7914675051252575e-06
- DR-03a c_s^2 = 4.4358017089341570e-06
- DR-04a c_s^2 = 3.4017829332315543e-06

## Pairwise normalized residuals (independent of g for g != 0)

- R_23 (DR-02a vs DR-03a) = 0.07422899055678828
- R_24 (DR-02a vs DR-04a) = 0.29003318302945985
- R_34 (DR-03a vs DR-04a) = 0.23310752904485865

Summary:

- R_max = 0.29003318302945985
- R_rms = 0.21906491457608293

## g-grid scan (tau_obs = 0.10)

Note: because obs is multiplicative in g, the normalized residuals are constant for all g > 0 (they cancel g).

| g | obs_DR02 | obs_DR03 | obs_DR04 | R_23 | R_24 | R_34 | R_max | retain |
|---:|---:|---:|---:|---:|---:|---:|---:|:---:|
| 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | yes |
| 0.1 | 4.791467505125257e-07 | 4.435801708934157e-07 | 3.401782933231554e-07 | 0.07422899055678828 | 0.29003318302945985 | 0.23310752904485865 | 0.29003318302945985 | no |
| 0.3 | 1.4374402515375773e-06 | 1.330740512680247e-06 | 1.0205348799694663e-06 | 0.07422899055678828 | 0.29003318302945985 | 0.23310752904485865 | 0.29003318302945985 | no |
| 0.6 | 2.8748805030751546e-06 | 2.661481025360494e-06 | 2.0410697599389326e-06 | 0.07422899055678828 | 0.29003318302945985 | 0.23310752904485865 | 0.29003318302945985 | no |
| 1.0 | 4.7914675051252575e-06 | 4.435801708934157e-06 | 3.4017829332315543e-06 | 0.07422899055678828 | 0.29003318302945985 | 0.23310752904485865 | 0.29003318302945985 | no |

## Interpretation

- Adding DR-04a (tighter low-k window) increases the cross-fit spread in c_s^2 enough that the multi-fit gate fails under tau_obs = 0.10 for any non-degenerate g.
- This is evidence that OV-01 (as currently defined) is not robust under this 3-window perturbation; the next logical upgrade is either (i) revise the observable to avoid g-cancellation in normalized residuals, or (ii) keep OV-01c as a robustness stress-test and use a different observable for ranking.

## Gate decision (with fit-quality context)

Fit-quality instrumentation (see `formal/markdown/locks/bridges/DR_fit_quality_comparison_DR02_DR03_DR04.md`) indicates:

- DR-04a uses fewer points (N=4), but its slope standard error is comparable to DR-03a and R^2 remains high.

Therefore, the current evidence does **not** support treating DR-04a as a purely “low-confidence perturbation” that should be excluded from robustness bookkeeping.
Under the provisional tau_obs = 0.10 rule, OV-01c reports robustness is not established in a way that is plausibly methodological *and/or* physical (fit-window sensitivity), not merely undersampling noise.
