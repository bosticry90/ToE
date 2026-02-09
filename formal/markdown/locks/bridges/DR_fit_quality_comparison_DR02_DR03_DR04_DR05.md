# DR Fit-Quality Comparison (DR-02a vs DR-03a vs DR-04a vs DR-05a)

Date: 2026-01-17

Purpose: distinguish monotone drift with k-max (systematic model mismatch / curvature) from localized outliers (window-endpoint interaction / digitization artifacts), while keeping the loop data-backed and deterministic.

All diagnostics below are computed deterministically from each artifact’s frozen `sample_kw` using a through-origin fit model:

- omega(k) ~= c_s * k

## Summary table

| ID | window (k max, um^-1) | N_points | c_s (m/s) | RMSE(omega) (rad/s) | slope_stderr (m/s) | R^2 (origin) | data_fingerprint |
|---:|---:|---:|---:|---:|---:|---:|:---|
| DR-02a | 3.2 | 9 | 0.0021889420972527477 | 296.12925363791106 | 5.3234711357089647e-05 | 0.9952906478115147 | 80c14686bbf4006939d1cdd9128ec4c7d6dffa90688c0b3463a6ff530e7ec5af |
| DR-03a | 2.1 | 6 | 0.0021061343045813002 | 294.70780462524556 | 9.634918571711478e-05 | 0.9896444499714963 | eb6bbfa1d6abd0312156719da60a862a215f67e83e313f5586fe80e2082e4a24 |
| DR-05a | 1.8 | 5 | 0.0019925867614031183 | 242.76304066265237 | 0.0001037106770711398 | 0.9892800758680620 | 4625f1556255e06a1c16408ee1c820da25d846f3ab53f91e446a975d505397b8 |
| DR-04a | 1.6 | 4 | 0.0018443922937465213 | 164.84385313492098 | 9.781878290939265e-05 | 0.9916322287424649 | c8971d8ba913dcc08e11e6995f72ee8ccecab832bc24483a94026b52045d804c |

## Monotonicity assessment

- c_s decreases as k-max shrinks: 3.2 → 2.1 → 1.8 → 1.6.
- Fit-quality does not collapse at DR-05a/DR-04a (stderr and R^2 remain comparable), which supports interpreting the drift as systematic window sensitivity rather than a single low-confidence outlier.

Next science escalation (queued): introduce a curvature-aware low-k model (e.g., omega/k ≈ c_s + β k^2) and re-run the same multi-fit envelope to see if the spread collapses without losing data-backed determinism.
