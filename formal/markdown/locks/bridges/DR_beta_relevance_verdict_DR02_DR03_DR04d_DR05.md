# DR-β-01 β relevance verdict — DR-02/03/04d/05 (curved)

Date: 2026-01-18

This report evaluates whether the curvature parameter $\beta$ in the proxy model $\omega/k = c_0 + \beta k^2$ is *inferentially meaningful* across the frozen curvature-aware DR window artifacts.

Inputs are strictly the frozen curved artifacts and their stamped fit-quality diagnostics.

## Decision criteria (predeclared)

Definitions:

- $\mathrm{SNR}(\beta) \equiv |\beta|/\mathrm{stderr}(\beta)$
- “Compatible with zero (2σ)” iff $|\beta| \le 2\,\mathrm{stderr}(\beta)$

Thresholds used in this report:

- “Detected” (decision-grade): $\mathrm{SNR}(\beta) \ge 2$
- “Sign stable across windows”: all windows have the same sign of $\beta$ (ignoring exact zeros)

## Sources

- `formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact_curved.json`
- `formal/external_evidence/bec_bragg_steinhauer_2001/dr03_fit_artifact_curved.json`
- `formal/external_evidence/bec_bragg_steinhauer_2001/dr04d_fit_artifact_curved.json`
- `formal/external_evidence/bec_bragg_steinhauer_2001/dr05_fit_artifact_curved.json`

## Table

| Window | N | data_fingerprint | β [s/m²] | stderr(β) [s/m²] | SNR(β) | sign(β) | |β|≤2σ? |
|---|---:|---|---:|---:|---:|:---:|:---:|
| DR-02 curved (k≤3.2) | 9 | 80c14686bbf4006939d1cdd9128ec4c7d6dffa90688c0b3463a6ff530e7ec5af | 2.3789270790166762e-17 | 2.7529466483225495e-17 | 0.8641384606803861 | + | yes |
| DR-03 curved (k≤2.1) | 6 | eb6bbfa1d6abd0312156719da60a862a215f67e83e313f5586fe80e2082e4a24 | 2.0543090235917590e-17 | 9.5830763157086800e-17 | 0.2143684299189305 | + | yes |
| DR-04d curved (k≤1.750000272...) | 5 | 4625f1556255e06a1c16408ee1c820da25d846f3ab53f91e446a975d505397b8 | -6.1687621091483440e-17 | 1.5868946466088918e-16 | 0.3887316730402144 | - | yes |
| DR-05 curved (k≤1.8) | 5 | 4625f1556255e06a1c16408ee1c820da25d846f3ab53f91e446a975d505397b8 | -6.1687621091483440e-17 | 1.5868946466088918e-16 | 0.3887316730402144 | - | yes |

## Verdict

- **β is not detected** in any window ($\mathrm{SNR}(\beta) < 2$ across the board).
- **β is compatible with zero (2σ)** in every window.
- **β sign is not stable across windows** (positive at higher-$k_{\max}$ windows; negative for the minimal feasible low-$k$ window).

Interpretation (restricted to the proxy model and frozen digitization): treat $\beta$ as **non-decision-grade / non-actionable** at present. Any workflow use of the curved proxy should not rely on $\beta$ being a resolved physical curvature parameter.

Note:
- Under the frozen Steinhauer Fig. 3a digitization, DR-04d and DR-05 select the same underlying 5-point sample (same `data_fingerprint`), so they are not statistically independent evidence about $\beta$.
