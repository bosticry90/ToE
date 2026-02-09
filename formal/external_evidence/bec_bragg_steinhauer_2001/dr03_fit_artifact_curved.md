# DR03 Curved Fit Artifact  Derived from Steinhauer Fig. 3a

Date: 2026-01-18

This file records a curvature-aware DR fit artifact computed deterministically from the frozen sample_kw points in the corresponding linear DR window artifact.

## Fit definition

We fit the proxy model:

- ω/k = c0 + β k

with u fixed to 0 (as in the linear artifacts).

## Result

- c0 = 0.0020438560232990946 m/s
- beta = 2.054309023591759e-17 s/m

## Fit quality (y = ω/k space)

- N_points = 6
- RMSE(ω/k) = 0.00028242195854024087 m/s
- stderr(c0) = 0.00022824378232785442 m/s
- stderr(beta) = 9.58307631570868e-17 s/m
- R(y-space) = 0.011357970394077044

## Provenance hash

- data_fingerprint (sha256): eb6bbfa1d6abd0312156719da60a862a215f67e83e313f5586fe80e2082e4a24
- fit_quality_fingerprint (sha256): a951bc6ca97eaac6d691bfc5a4c0d53973ba6a833875da8ad36c16b5838a1218

The complete artifact (including the sample) is stored in:

- ormal/external_evidence/bec_bragg_steinhauer_2001/dr03_fit_artifact_curved.json
