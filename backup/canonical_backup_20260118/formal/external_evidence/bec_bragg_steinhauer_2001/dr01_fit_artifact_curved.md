# DR02 Curved Fit Artifact  Derived from Steinhauer Fig. 3a

Date: 2026-01-18

This file records a curvature-aware DR fit artifact computed deterministically from the frozen sample_kw points in the corresponding linear DR window artifact.

## Fit definition

We fit the proxy model:

- ω/k = c0 + β k

with u fixed to 0 (as in the linear artifacts).

## Result

- c0 = 0.002033944912305306 m/s
- beta = 2.3789270790166762e-17 s/m

## Fit quality (y = ω/k space)

- N_points = 9
- RMSE(ω/k) = 0.0002330787248132785 m/s
- stderr(c0) = 0.0001382007978234305 m/s
- stderr(beta) = 2.7529466483225495e-17 s/m
- R(y-space) = 0.09639354544997059

## Provenance hash

- data_fingerprint (sha256): 80c14686bbf4006939d1cdd9128ec4c7d6dffa90688c0b3463a6ff530e7ec5af
- fit_quality_fingerprint (sha256): 10e33842da23f545d62614da36d260b6c703aa834535ba66e27574534c924f61

The complete artifact (including the sample) is stored in:

- ormal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact_curved.json
