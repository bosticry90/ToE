# DR04 Curved Fit Artifact  Derived from Steinhauer Fig. 3a

Date: 2026-01-18

This file records a curvature-aware DR fit artifact computed deterministically from the frozen sample_kw points in the corresponding linear DR window artifact.

## Fit definition

We fit the proxy model:

- ω/k = c0 + β k

with u fixed to 0 (as in the linear artifacts).

## Result

- c0 = 0.002317436007712101 m/s
- beta = -3.2630267536535073e-16 s/m

## Fit quality (y = ω/k space)

- N_points = 4
- RMSE(ω/k) = 0.00022921439968839546 m/s
- stderr(c0) = 0.00027513695206787586 m/s
- stderr(beta) = 2.3486522927841644e-16 s/m
- R(y-space) = 0.4911209111156265

## Provenance hash

- data_fingerprint (sha256): c8971d8ba913dcc08e11e6995f72ee8ccecab832bc24483a94026b52045d804c
- fit_quality_fingerprint (sha256): b8d10887a04d1dcf8f8eba521c73d7923080fe3c58b28efdef8515904bd5c1e8

The complete artifact (including the sample) is stored in:

- ormal/external_evidence/bec_bragg_steinhauer_2001/dr04_fit_artifact_curved.json
