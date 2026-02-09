# DR Fit-Quality Comparison (DR-02a vs DR-03a vs DR-04a)

Date: 2026-01-17

Purpose: separate “methodology signal” (fit-quality degradation under tight windows) from “science signal” (true instability of the low-k linearization across windows).

All diagnostics below are computed deterministically from each artifact’s frozen `sample_kw` using a through-origin fit model:

- omega(k) ~= c_s * k

## Summary table

| ID | window (k max, um^-1) | N_points | c_s (m/s) | RMSE(omega) (rad/s) | slope_stderr (m/s) | R^2 (origin) | data_fingerprint |
|---:|---:|---:|---:|---:|---:|---:|:---|
| DR-02a | 3.2 | 9 | 0.0021889420972527477 | 296.12925363791106 | 5.3234711357089647e-05 | 0.9952906478115147 | 80c14686bbf4006939d1cdd9128ec4c7d6dffa90688c0b3463a6ff530e7ec5af |
| DR-03a | 2.1 | 6 | 0.0021061343045813002 | 294.70780462524556 | 9.634918571711478e-05 | 0.9896444499714963 | eb6bbfa1d6abd0312156719da60a862a215f67e83e313f5586fe80e2082e4a24 |
| DR-04a | 1.6 | 4 | 0.0018443922937465213 | 164.84385313492098 | 9.781878290939265e-05 | 0.9916322287424649 | c8971d8ba913dcc08e11e6995f72ee8ccecab832bc24483a94026b52045d804c |

## Interpretation (methodology vs science)

- DR-04a has fewer points (N=4), but its slope standard error is comparable to DR-03a and its R^2 remains high.
- Under these diagnostics, DR-04a does **not** look like an obviously “low-confidence outlier” solely due to undersampling; the observed shift in c_s is therefore plausibly a real fit-window sensitivity (i.e., the low-k linearization is not stable across these windows).
- The remaining ambiguity is curvature/nonlinearity: a through-origin linear model may be too brittle, so a next escalation would be (i) add an intermediate window (DR-05) to see monotone drift vs outlier behavior, and/or (ii) fit a slightly richer low-k model (e.g., allow small curvature term) while preserving determinism.
