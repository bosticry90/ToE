# DR-04c Curved Fit Artifact — Derived from Steinhauer Fig. 3a

Date: 2026-01-18

This file records a curvature-aware DR fit artifact computed deterministically from the frozen `sample_kw` points in the corresponding linear DR-04c window artifact.

## Fit definition

We fit the proxy model (with u fixed to 0, as in the linear artifacts):

- ω/k = c0 + β k^2

## Result

- c0 = 0.0020571307304609546 m/s
- beta = 1.0695160608950022e-17 s/m^2

## Fit quality (y = ω/k space)

- N_points = 7
- RMSE(ω/k) = 0.0002621208907909953 m/s
- stderr(c0) = 0.00018643214868942557 m/s
- stderr(beta) = 5.88331279592936e-17 s/m^2
- R^2(y-space) = 0.006565983183123181

## Provenance hash

- data_fingerprint (sha256): 68480ae926b58d56a9dee08263584aedc9167460ecb470539c0c2a47a0a1ee01
- fit_quality_fingerprint (sha256): 61973da27d4dd37c489fb99e3f4cece0cedd92648f43578ca08be1dd7ada08a9

The complete artifact (including the sample) is stored in:

- `formal/external_evidence/bec_bragg_steinhauer_2001/dr04c_fit_artifact_curved.json`
